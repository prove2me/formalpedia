-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch00
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch00
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:36:20.824051+00:00
-- url     : https://prove2.me/theorems/7c6da3aa-0ed5-46cf-af51-ad23b14f5ac4
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Entries / Batch00
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch00` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch00

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection000 : Projection := ⟨1,0,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup000 : projections[0]! = nestingProjection000 := by
  rw [projections_lookup]
  rfl
def nestingEntries000 (n : Nat) : Int := if n < 64 then 0 else 0
theorem nestingEntries_eq000 (n : Nat) :
    nestingProjection000.numerator[n]! = nestingEntries000 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries000, if_neg (by omega : ¬ n < 64)]

def nestingProjection001 : Projection := ⟨1,8,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup001 : projections[1]! = nestingProjection001 := by
  rw [projections_lookup]
  rfl
def nestingEntries001 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq001 (n : Nat) :
    nestingProjection001.numerator[n]! = nestingEntries001 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries001, if_neg (by omega : ¬ n < 64)]

def nestingProjection002 : Projection := ⟨1,1,#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup002 : projections[2]! = nestingProjection002 := by
  rw [projections_lookup]
  rfl
def nestingEntries002 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else 0) else 0) else 0) else 0
theorem nestingEntries_eq002 (n : Nat) :
    nestingProjection002.numerator[n]! = nestingEntries002 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries002, if_neg (by omega : ¬ n < 64)]

def nestingProjection003 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup003 : projections[3]! = nestingProjection003 := by
  rw [projections_lookup]
  rfl
def nestingEntries003 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else 0) else 0) else 0
theorem nestingEntries_eq003 (n : Nat) :
    nestingProjection003.numerator[n]! = nestingEntries003 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries003, if_neg (by omega : ¬ n < 64)]

def nestingProjection004 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup004 : projections[4]! = nestingProjection004 := by
  rw [projections_lookup]
  rfl
def nestingEntries004 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else 0)) else 0) else 0
theorem nestingEntries_eq004 (n : Nat) :
    nestingProjection004.numerator[n]! = nestingEntries004 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries004, if_neg (by omega : ¬ n < 64)]

def nestingProjection005 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup005 : projections[5]! = nestingProjection005 := by
  rw [projections_lookup]
  rfl
def nestingEntries005 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq005 (n : Nat) :
    nestingProjection005.numerator[n]! = nestingEntries005 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries005, if_neg (by omega : ¬ n < 64)]

def nestingProjection006 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup006 : projections[6]! = nestingProjection006 := by
  rw [projections_lookup]
  rfl
def nestingEntries006 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else 0)) else 0
theorem nestingEntries_eq006 (n : Nat) :
    nestingProjection006.numerator[n]! = nestingEntries006 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries006, if_neg (by omega : ¬ n < 64)]

def nestingProjection007 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup007 : projections[7]! = nestingProjection007 := by
  rw [projections_lookup]
  rfl
def nestingEntries007 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq007 (n : Nat) :
    nestingProjection007.numerator[n]! = nestingEntries007 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries007, if_neg (by omega : ¬ n < 64)]

def nestingProjection008 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup008 : projections[8]! = nestingProjection008 := by
  rw [projections_lookup]
  rfl
def nestingEntries008 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then 0 else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq008 (n : Nat) :
    nestingProjection008.numerator[n]! = nestingEntries008 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries008, if_neg (by omega : ¬ n < 64)]

def nestingProjection009 : Projection := ⟨1,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup009 : projections[9]! = nestingProjection009 := by
  rw [projections_lookup]
  rfl
def nestingEntries009 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then 0 else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq009 (n : Nat) :
    nestingProjection009.numerator[n]! = nestingEntries009 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries009, if_neg (by omega : ¬ n < 64)]

def nestingProjection010 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,1]⟩
theorem nestingLookup010 : projections[10]! = nestingProjection010 := by
  rw [projections_lookup]
  rfl
def nestingEntries010 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq010 (n : Nat) :
    nestingProjection010.numerator[n]! = nestingEntries010 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries010, if_neg (by omega : ¬ n < 64)]

def nestingProjection011 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,-1,0,0,1]⟩
theorem nestingLookup011 : projections[11]! = nestingProjection011 := by
  rw [projections_lookup]
  rfl
def nestingEntries011 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq011 (n : Nat) :
    nestingProjection011.numerator[n]! = nestingEntries011 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries011, if_neg (by omega : ¬ n < 64)]

def nestingProjection012 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,0,0,0,0,0,0,0,0,0,-1,-1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,1,0,0,1]⟩
theorem nestingLookup012 : projections[12]! = nestingProjection012 := by
  rw [projections_lookup]
  rfl
def nestingEntries012 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq012 (n : Nat) :
    nestingProjection012.numerator[n]! = nestingEntries012 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries012, if_neg (by omega : ¬ n < 64)]

def nestingProjection013 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,0,-1,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1]⟩
theorem nestingLookup013 : projections[13]! = nestingProjection013 := by
  rw [projections_lookup]
  rfl
def nestingEntries013 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq013 (n : Nat) :
    nestingProjection013.numerator[n]! = nestingEntries013 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries013, if_neg (by omega : ¬ n < 64)]

def nestingProjection014 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,-1,0,-1,1,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,0,0,1]⟩
theorem nestingLookup014 : projections[14]! = nestingProjection014 := by
  rw [projections_lookup]
  rfl
def nestingEntries014 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq014 (n : Nat) :
    nestingProjection014.numerator[n]! = nestingEntries014 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries014, if_neg (by omega : ¬ n < 64)]

def nestingProjection015 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,-1,0,0,1,0,-1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,-1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,-1,0,0,1]⟩
theorem nestingLookup015 : projections[15]! = nestingProjection015 := by
  rw [projections_lookup]
  rfl
def nestingEntries015 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq015 (n : Nat) :
    nestingProjection015.numerator[n]! = nestingEntries015 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries015, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection016 : Projection := ⟨4,1,#[1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup016 : projections[16]! = nestingProjection016 := by
  rw [projections_lookup]
  rfl
def nestingEntries016 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq016 (n : Nat) :
    nestingProjection016.numerator[n]! = nestingEntries016 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries016, if_neg (by omega : ¬ n < 64)]

def nestingProjection017 : Projection := ⟨4,1,#[1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup017 : projections[17]! = nestingProjection017 := by
  rw [projections_lookup]
  rfl
def nestingEntries017 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq017 (n : Nat) :
    nestingProjection017.numerator[n]! = nestingEntries017 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries017, if_neg (by omega : ¬ n < 64)]

def nestingProjection018 : Projection := ⟨4,1,#[1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup018 : projections[18]! = nestingProjection018 := by
  rw [projections_lookup]
  rfl
def nestingEntries018 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq018 (n : Nat) :
    nestingProjection018.numerator[n]! = nestingEntries018 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries018, if_neg (by omega : ¬ n < 64)]

def nestingProjection019 : Projection := ⟨4,1,#[1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup019 : projections[19]! = nestingProjection019 := by
  rw [projections_lookup]
  rfl
def nestingEntries019 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq019 (n : Nat) :
    nestingProjection019.numerator[n]! = nestingEntries019 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries019, if_neg (by omega : ¬ n < 64)]

def nestingProjection020 : Projection := ⟨4,1,#[1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup020 : projections[20]! = nestingProjection020 := by
  rw [projections_lookup]
  rfl
def nestingEntries020 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq020 (n : Nat) :
    nestingProjection020.numerator[n]! = nestingEntries020 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries020, if_neg (by omega : ¬ n < 64)]

def nestingProjection021 : Projection := ⟨4,1,#[1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup021 : projections[21]! = nestingProjection021 := by
  rw [projections_lookup]
  rfl
def nestingEntries021 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq021 (n : Nat) :
    nestingProjection021.numerator[n]! = nestingEntries021 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries021, if_neg (by omega : ¬ n < 64)]

def nestingProjection022 : Projection := ⟨4,1,#[1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup022 : projections[22]! = nestingProjection022 := by
  rw [projections_lookup]
  rfl
def nestingEntries022 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq022 (n : Nat) :
    nestingProjection022.numerator[n]! = nestingEntries022 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries022, if_neg (by omega : ¬ n < 64)]

def nestingProjection023 : Projection := ⟨4,1,#[1,0,-1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup023 : projections[23]! = nestingProjection023 := by
  rw [projections_lookup]
  rfl
def nestingEntries023 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq023 (n : Nat) :
    nestingProjection023.numerator[n]! = nestingEntries023 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries023, if_neg (by omega : ¬ n < 64)]

def nestingProjection024 : Projection := ⟨4,1,#[1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1]⟩
theorem nestingLookup024 : projections[24]! = nestingProjection024 := by
  rw [projections_lookup]
  rfl
def nestingEntries024 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else 1))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq024 (n : Nat) :
    nestingProjection024.numerator[n]! = nestingEntries024 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries024, if_neg (by omega : ¬ n < 64)]

def nestingProjection025 : Projection := ⟨4,1,#[1,1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,-1,-1,-1,0,0,0,0,-1,1]⟩
theorem nestingLookup025 : projections[25]! = nestingProjection025 := by
  rw [projections_lookup]
  rfl
def nestingEntries025 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq025 (n : Nat) :
    nestingProjection025.numerator[n]! = nestingEntries025 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries025, if_neg (by omega : ¬ n < 64)]

def nestingProjection026 : Projection := ⟨4,1,#[1,1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,-1,1]⟩
theorem nestingLookup026 : projections[26]! = nestingProjection026 := by
  rw [projections_lookup]
  rfl
def nestingEntries026 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq026 (n : Nat) :
    nestingProjection026.numerator[n]! = nestingEntries026 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries026, if_neg (by omega : ¬ n < 64)]

def nestingProjection027 : Projection := ⟨4,1,#[1,1,0,0,0,0,-1,-1,1,1,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,0,0,1,1,-1,-1,0,0,0,0,1,1]⟩
theorem nestingLookup027 : projections[27]! = nestingProjection027 := by
  rw [projections_lookup]
  rfl
def nestingEntries027 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else (-1)))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq027 (n : Nat) :
    nestingProjection027.numerator[n]! = nestingEntries027 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries027, if_neg (by omega : ¬ n < 64)]

def nestingProjection028 : Projection := ⟨4,1,#[1,-1,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1]⟩
theorem nestingLookup028 : projections[28]! = nestingProjection028 := by
  rw [projections_lookup]
  rfl
def nestingEntries028 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (-1)))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq028 (n : Nat) :
    nestingProjection028.numerator[n]! = nestingEntries028 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries028, if_neg (by omega : ¬ n < 64)]

def nestingProjection029 : Projection := ⟨4,1,#[1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1]⟩
theorem nestingLookup029 : projections[29]! = nestingProjection029 := by
  rw [projections_lookup]
  rfl
def nestingEntries029 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq029 (n : Nat) :
    nestingProjection029.numerator[n]! = nestingEntries029 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries029, if_neg (by omega : ¬ n < 64)]

def nestingProjection030 : Projection := ⟨4,1,#[1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1]⟩
theorem nestingLookup030 : projections[30]! = nestingProjection030 := by
  rw [projections_lookup]
  rfl
def nestingEntries030 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq030 (n : Nat) :
    nestingProjection030.numerator[n]! = nestingEntries030 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries030, if_neg (by omega : ¬ n < 64)]

def nestingProjection031 : Projection := ⟨4,1,#[1,-1,0,0,0,0,-1,-1,-1,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,1,-1,1,0,0,0,0,1,1]⟩
theorem nestingLookup031 : projections[31]! = nestingProjection031 := by
  rw [projections_lookup]
  rfl
def nestingEntries031 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else 1))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq031 (n : Nat) :
    nestingProjection031.numerator[n]! = nestingEntries031 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries031, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection032 : Projection := ⟨4,1,#[1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup032 : projections[32]! = nestingProjection032 := by
  rw [projections_lookup]
  rfl
def nestingEntries032 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 1 else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq032 (n : Nat) :
    nestingProjection032.numerator[n]! = nestingEntries032 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries032, if_neg (by omega : ¬ n < 64)]

def nestingProjection033 : Projection := ⟨4,1,#[1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup033 : projections[33]! = nestingProjection033 := by
  rw [projections_lookup]
  rfl
def nestingEntries033 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq033 (n : Nat) :
    nestingProjection033.numerator[n]! = nestingEntries033 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries033, if_neg (by omega : ¬ n < 64)]

def nestingProjection034 : Projection := ⟨4,1,#[1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup034 : projections[34]! = nestingProjection034 := by
  rw [projections_lookup]
  rfl
def nestingEntries034 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq034 (n : Nat) :
    nestingProjection034.numerator[n]! = nestingEntries034 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries034, if_neg (by omega : ¬ n < 64)]

def nestingProjection035 : Projection := ⟨4,1,#[1,1,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup035 : projections[35]! = nestingProjection035 := by
  rw [projections_lookup]
  rfl
def nestingEntries035 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (-1) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq035 (n : Nat) :
    nestingProjection035.numerator[n]! = nestingEntries035 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries035, if_neg (by omega : ¬ n < 64)]

def nestingProjection036 : Projection := ⟨4,1,#[1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup036 : projections[36]! = nestingProjection036 := by
  rw [projections_lookup]
  rfl
def nestingEntries036 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (-1) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq036 (n : Nat) :
    nestingProjection036.numerator[n]! = nestingEntries036 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries036, if_neg (by omega : ¬ n < 64)]

def nestingProjection037 : Projection := ⟨4,1,#[1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup037 : projections[37]! = nestingProjection037 := by
  rw [projections_lookup]
  rfl
def nestingEntries037 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq037 (n : Nat) :
    nestingProjection037.numerator[n]! = nestingEntries037 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries037, if_neg (by omega : ¬ n < 64)]

def nestingProjection038 : Projection := ⟨4,1,#[1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup038 : projections[38]! = nestingProjection038 := by
  rw [projections_lookup]
  rfl
def nestingEntries038 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq038 (n : Nat) :
    nestingProjection038.numerator[n]! = nestingEntries038 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries038, if_neg (by omega : ¬ n < 64)]

def nestingProjection039 : Projection := ⟨4,1,#[1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup039 : projections[39]! = nestingProjection039 := by
  rw [projections_lookup]
  rfl
def nestingEntries039 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 1 else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq039 (n : Nat) :
    nestingProjection039.numerator[n]! = nestingEntries039 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries039, if_neg (by omega : ¬ n < 64)]

def nestingProjection040 : Projection := ⟨4,1,#[1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1]⟩
theorem nestingLookup040 : projections[40]! = nestingProjection040 := by
  rw [projections_lookup]
  rfl
def nestingEntries040 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq040 (n : Nat) :
    nestingProjection040.numerator[n]! = nestingEntries040 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries040, if_neg (by omega : ¬ n < 64)]

def nestingProjection041 : Projection := ⟨4,1,#[1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,-1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup041 : projections[41]! = nestingProjection041 := by
  rw [projections_lookup]
  rfl
def nestingEntries041 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq041 (n : Nat) :
    nestingProjection041.numerator[n]! = nestingEntries041 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries041, if_neg (by omega : ¬ n < 64)]

def nestingProjection042 : Projection := ⟨4,1,#[1,0,1,0,0,-1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1,0,0,1,0,-1,0,0,0,0,0,0,0,0,1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup042 : projections[42]! = nestingProjection042 := by
  rw [projections_lookup]
  rfl
def nestingEntries042 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq042 (n : Nat) :
    nestingProjection042.numerator[n]! = nestingEntries042 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries042, if_neg (by omega : ¬ n < 64)]

def nestingProjection043 : Projection := ⟨4,1,#[1,0,1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,1,0,1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1,0,0,1,0,1,0,0,0,0,0,0,0,0,-1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup043 : projections[43]! = nestingProjection043 := by
  rw [projections_lookup]
  rfl
def nestingEntries043 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq043 (n : Nat) :
    nestingProjection043.numerator[n]! = nestingEntries043 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries043, if_neg (by omega : ¬ n < 64)]

def nestingProjection044 : Projection := ⟨4,1,#[1,0,-1,0,0,1,0,1,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup044 : projections[44]! = nestingProjection044 := by
  rw [projections_lookup]
  rfl
def nestingEntries044 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq044 (n : Nat) :
    nestingProjection044.numerator[n]! = nestingEntries044 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries044, if_neg (by omega : ¬ n < 64)]

def nestingProjection045 : Projection := ⟨4,1,#[1,0,-1,0,0,1,0,-1,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,1,0,-1,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup045 : projections[45]! = nestingProjection045 := by
  rw [projections_lookup]
  rfl
def nestingEntries045 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq045 (n : Nat) :
    nestingProjection045.numerator[n]! = nestingEntries045 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries045, if_neg (by omega : ¬ n < 64)]

def nestingProjection046 : Projection := ⟨4,1,#[1,0,-1,0,0,-1,0,1,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup046 : projections[46]! = nestingProjection046 := by
  rw [projections_lookup]
  rfl
def nestingEntries046 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq046 (n : Nat) :
    nestingProjection046.numerator[n]! = nestingEntries046 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries046, if_neg (by omega : ¬ n < 64)]

def nestingProjection047 : Projection := ⟨4,1,#[1,0,-1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,1]⟩
theorem nestingLookup047 : projections[47]! = nestingProjection047 := by
  rw [projections_lookup]
  rfl
def nestingEntries047 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq047 (n : Nat) :
    nestingProjection047.numerator[n]! = nestingEntries047 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries047, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection048 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup048 : projections[48]! = nestingProjection048 := by
  rw [projections_lookup]
  rfl
def nestingEntries048 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq048 (n : Nat) :
    nestingProjection048.numerator[n]! = nestingEntries048 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries048, if_neg (by omega : ¬ n < 64)]

def nestingProjection049 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup049 : projections[49]! = nestingProjection049 := by
  rw [projections_lookup]
  rfl
def nestingEntries049 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq049 (n : Nat) :
    nestingProjection049.numerator[n]! = nestingEntries049 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries049, if_neg (by omega : ¬ n < 64)]

def nestingProjection050 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup050 : projections[50]! = nestingProjection050 := by
  rw [projections_lookup]
  rfl
def nestingEntries050 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq050 (n : Nat) :
    nestingProjection050.numerator[n]! = nestingEntries050 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries050, if_neg (by omega : ¬ n < 64)]

def nestingProjection051 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup051 : projections[51]! = nestingProjection051 := by
  rw [projections_lookup]
  rfl
def nestingEntries051 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq051 (n : Nat) :
    nestingProjection051.numerator[n]! = nestingEntries051 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries051, if_neg (by omega : ¬ n < 64)]

def nestingProjection052 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup052 : projections[52]! = nestingProjection052 := by
  rw [projections_lookup]
  rfl
def nestingEntries052 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq052 (n : Nat) :
    nestingProjection052.numerator[n]! = nestingEntries052 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries052, if_neg (by omega : ¬ n < 64)]

def nestingProjection053 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup053 : projections[53]! = nestingProjection053 := by
  rw [projections_lookup]
  rfl
def nestingEntries053 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq053 (n : Nat) :
    nestingProjection053.numerator[n]! = nestingEntries053 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries053, if_neg (by omega : ¬ n < 64)]

def nestingProjection054 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,-1,-1,-1,1]⟩
theorem nestingLookup054 : projections[54]! = nestingProjection054 := by
  rw [projections_lookup]
  rfl
def nestingEntries054 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then 1 else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 1 else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq054 (n : Nat) :
    nestingProjection054.numerator[n]! = nestingEntries054 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries054, if_neg (by omega : ¬ n < 64)]

def nestingProjection055 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,1,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,1,-1,0,0,0,0,1,1,-1,1]⟩
theorem nestingLookup055 : projections[55]! = nestingProjection055 := by
  rw [projections_lookup]
  rfl
def nestingEntries055 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then 1 else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq055 (n : Nat) :
    nestingProjection055.numerator[n]! = nestingEntries055 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries055, if_neg (by omega : ¬ n < 64)]

def nestingProjection056 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,-1,0,0,0,0,1,1,-1,-1,0,0,0,0,-1,-1,1,1,0,0,0,0,-1,-1,1,1]⟩
theorem nestingLookup056 : projections[56]! = nestingProjection056 := by
  rw [projections_lookup]
  rfl
def nestingEntries056 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (-1))) else (if n < 44 then 0 else (if n < 46 then 1 else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else 1)) else (if n < 60 then 0 else (if n < 62 then (-1) else 1))))) else 0
theorem nestingEntries_eq056 (n : Nat) :
    nestingProjection056.numerator[n]! = nestingEntries056 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries056, if_neg (by omega : ¬ n < 64)]

def nestingProjection057 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,1,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,1,1]⟩
theorem nestingLookup057 : projections[57]! = nestingProjection057 := by
  rw [projections_lookup]
  rfl
def nestingEntries057 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else 1)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else 1)) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else 1))))) else 0
theorem nestingEntries_eq057 (n : Nat) :
    nestingProjection057.numerator[n]! = nestingEntries057 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries057, if_neg (by omega : ¬ n < 64)]

def nestingProjection058 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1,-1,1]⟩
theorem nestingLookup058 : projections[58]! = nestingProjection058 := by
  rw [projections_lookup]
  rfl
def nestingEntries058 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq058 (n : Nat) :
    nestingProjection058.numerator[n]! = nestingEntries058 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries058, if_neg (by omega : ¬ n < 64)]

def nestingProjection059 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1]⟩
theorem nestingLookup059 : projections[59]! = nestingProjection059 := by
  rw [projections_lookup]
  rfl
def nestingEntries059 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq059 (n : Nat) :
    nestingProjection059.numerator[n]! = nestingEntries059 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries059, if_neg (by omega : ¬ n < 64)]

def nestingProjection060 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,-1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1]⟩
theorem nestingLookup060 : projections[60]! = nestingProjection060 := by
  rw [projections_lookup]
  rfl
def nestingEntries060 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (-1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else 1))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else 1)) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else 1))))) else 0
theorem nestingEntries_eq060 (n : Nat) :
    nestingProjection060.numerator[n]! = nestingEntries060 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries060, if_neg (by omega : ¬ n < 64)]

def nestingProjection061 : Projection := ⟨4,1,#[1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup061 : projections[61]! = nestingProjection061 := by
  rw [projections_lookup]
  rfl
def nestingEntries061 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then 1 else 0) else (if n < 12 then 1 else 0)) else (if n < 24 then (if n < 20 then 1 else 0) else (if n < 28 then 1 else 0))) else 0) else 0
theorem nestingEntries_eq061 (n : Nat) :
    nestingProjection061.numerator[n]! = nestingEntries061 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries061, if_neg (by omega : ¬ n < 64)]

def nestingProjection062 : Projection := ⟨4,1,#[1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,-1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup062 : projections[62]! = nestingProjection062 := by
  rw [projections_lookup]
  rfl
def nestingEntries062 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then 1 else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then (-1) else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq062 (n : Nat) :
    nestingProjection062.numerator[n]! = nestingEntries062 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries062, if_neg (by omega : ¬ n < 64)]

def nestingProjection063 : Projection := ⟨4,1,#[1,1,-1,-1,0,0,0,0,1,1,-1,-1,0,0,0,0,-1,-1,1,1,0,0,0,0,-1,-1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup063 : projections[63]! = nestingProjection063 := by
  rw [projections_lookup]
  rfl
def nestingEntries063 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else (-1)) else 0) else (if n < 12 then (if n < 10 then 1 else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else 1) else 0) else (if n < 28 then (if n < 26 then (-1) else 1) else 0))) else 0) else 0
theorem nestingEntries_eq063 (n : Nat) :
    nestingProjection063.numerator[n]! = nestingEntries063 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries063, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection064 : Projection := ⟨4,1,#[1,-1,1,1,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup064 : projections[64]! = nestingProjection064 := by
  rw [projections_lookup]
  rfl
def nestingEntries064 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 1) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else 1) else 0))) else 0) else 0
theorem nestingEntries_eq064 (n : Nat) :
    nestingProjection064.numerator[n]! = nestingEntries064 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries064, if_neg (by omega : ¬ n < 64)]

def nestingProjection065 : Projection := ⟨4,1,#[1,-1,1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup065 : projections[65]! = nestingProjection065 := by
  rw [projections_lookup]
  rfl
def nestingEntries065 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else (if n < 27 then (-1) else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq065 (n : Nat) :
    nestingProjection065.numerator[n]! = nestingEntries065 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries065, if_neg (by omega : ¬ n < 64)]

def nestingProjection066 : Projection := ⟨4,1,#[1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup066 : projections[66]! = nestingProjection066 := by
  rw [projections_lookup]
  rfl
def nestingEntries066 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq066 (n : Nat) :
    nestingProjection066.numerator[n]! = nestingEntries066 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries066, if_neg (by omega : ¬ n < 64)]

def nestingProjection067 : Projection := ⟨4,1,#[1,-1,-1,-1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup067 : projections[67]! = nestingProjection067 := by
  rw [projections_lookup]
  rfl
def nestingEntries067 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else 1) else 0))) else 0) else 0
theorem nestingEntries_eq067 (n : Nat) :
    nestingProjection067.numerator[n]! = nestingEntries067 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries067, if_neg (by omega : ¬ n < 64)]

def nestingProjection068 : Projection := ⟨4,1,#[1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,-1,-1,0,0,1]⟩
theorem nestingLookup068 : projections[68]! = nestingProjection068 := by
  rw [projections_lookup]
  rfl
def nestingEntries068 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq068 (n : Nat) :
    nestingProjection068.numerator[n]! = nestingEntries068 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries068, if_neg (by omega : ¬ n < 64)]

def nestingProjection069 : Projection := ⟨4,1,#[1,0,0,1,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup069 : projections[69]! = nestingProjection069 := by
  rw [projections_lookup]
  rfl
def nestingEntries069 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq069 (n : Nat) :
    nestingProjection069.numerator[n]! = nestingEntries069 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries069, if_neg (by omega : ¬ n < 64)]

def nestingProjection070 : Projection := ⟨4,1,#[1,0,0,1,-1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,-1,1,0,0,1]⟩
theorem nestingLookup070 : projections[70]! = nestingProjection070 := by
  rw [projections_lookup]
  rfl
def nestingEntries070 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq070 (n : Nat) :
    nestingProjection070.numerator[n]! = nestingEntries070 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries070, if_neg (by omega : ¬ n < 64)]

def nestingProjection071 : Projection := ⟨4,1,#[1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,1,0,0,1]⟩
theorem nestingLookup071 : projections[71]! = nestingProjection071 := by
  rw [projections_lookup]
  rfl
def nestingEntries071 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq071 (n : Nat) :
    nestingProjection071.numerator[n]! = nestingEntries071 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries071, if_neg (by omega : ¬ n < 64)]

def nestingProjection072 : Projection := ⟨4,1,#[1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup072 : projections[72]! = nestingProjection072 := by
  rw [projections_lookup]
  rfl
def nestingEntries072 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq072 (n : Nat) :
    nestingProjection072.numerator[n]! = nestingEntries072 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries072, if_neg (by omega : ¬ n < 64)]

def nestingProjection073 : Projection := ⟨4,1,#[1,0,0,-1,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,-1,0,0,1]⟩
theorem nestingLookup073 : projections[73]! = nestingProjection073 := by
  rw [projections_lookup]
  rfl
def nestingEntries073 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq073 (n : Nat) :
    nestingProjection073.numerator[n]! = nestingEntries073 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries073, if_neg (by omega : ¬ n < 64)]

def nestingProjection074 : Projection := ⟨4,1,#[1,0,0,-1,-1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,1,0,0,1]⟩
theorem nestingLookup074 : projections[74]! = nestingProjection074 := by
  rw [projections_lookup]
  rfl
def nestingEntries074 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq074 (n : Nat) :
    nestingProjection074.numerator[n]! = nestingEntries074 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries074, if_neg (by omega : ¬ n < 64)]

def nestingProjection075 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup075 : projections[75]! = nestingProjection075 := by
  rw [projections_lookup]
  rfl
def nestingEntries075 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq075 (n : Nat) :
    nestingProjection075.numerator[n]! = nestingEntries075 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries075, if_neg (by omega : ¬ n < 64)]

def nestingProjection076 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,1,0,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,-1,0,0,1,0,1,1,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,-1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup076 : projections[76]! = nestingProjection076 := by
  rw [projections_lookup]
  rfl
def nestingEntries076 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq076 (n : Nat) :
    nestingProjection076.numerator[n]! = nestingEntries076 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries076, if_neg (by omega : ¬ n < 64)]

def nestingProjection077 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,-1,0,1,0,0,0,0,0,0,0,0,0,0,1,0,1,-1,0,1,0,0,-1,0,-1,1,0,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup077 : projections[77]! = nestingProjection077 := by
  rw [projections_lookup]
  rfl
def nestingEntries077 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq077 (n : Nat) :
    nestingProjection077.numerator[n]! = nestingEntries077 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries077, if_neg (by omega : ¬ n < 64)]

def nestingProjection078 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,-1,0,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0,0,-1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup078 : projections[78]! = nestingProjection078 := by
  rw [projections_lookup]
  rfl
def nestingEntries078 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq078 (n : Nat) :
    nestingProjection078.numerator[n]! = nestingEntries078 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries078, if_neg (by omega : ¬ n < 64)]

def nestingProjection079 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,-1,0,-1,0,0,1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0,0,1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup079 : projections[79]! = nestingProjection079 := by
  rw [projections_lookup]
  rfl
def nestingEntries079 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq079 (n : Nat) :
    nestingProjection079.numerator[n]! = nestingEntries079 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries079, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection080 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,1,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup080 : projections[80]! = nestingProjection080 := by
  rw [projections_lookup]
  rfl
def nestingEntries080 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq080 (n : Nat) :
    nestingProjection080.numerator[n]! = nestingEntries080 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries080, if_neg (by omega : ¬ n < 64)]

def nestingProjection081 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,-1,0,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,0,0,0,0,0,0,0,0,0,1,0,-1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup081 : projections[81]! = nestingProjection081 := by
  rw [projections_lookup]
  rfl
def nestingEntries081 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq081 (n : Nat) :
    nestingProjection081.numerator[n]! = nestingEntries081 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries081, if_neg (by omega : ¬ n < 64)]

def nestingProjection082 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,1,0,1,0,0,-1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup082 : projections[82]! = nestingProjection082 := by
  rw [projections_lookup]
  rfl
def nestingEntries082 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq082 (n : Nat) :
    nestingProjection082.numerator[n]! = nestingEntries082 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries082, if_neg (by omega : ¬ n < 64)]

def nestingProjection083 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1]⟩
theorem nestingLookup083 : projections[83]! = nestingProjection083 := by
  rw [projections_lookup]
  rfl
def nestingEntries083 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else 1)))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq083 (n : Nat) :
    nestingProjection083.numerator[n]! = nestingEntries083 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries083, if_neg (by omega : ¬ n < 64)]

def nestingProjection084 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1]⟩
theorem nestingLookup084 : projections[84]! = nestingProjection084 := by
  rw [projections_lookup]
  rfl
def nestingEntries084 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq084 (n : Nat) :
    nestingProjection084.numerator[n]! = nestingEntries084 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries084, if_neg (by omega : ¬ n < 64)]

def nestingProjection085 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,1,1]⟩
theorem nestingLookup085 : projections[85]! = nestingProjection085 := by
  rw [projections_lookup]
  rfl
def nestingEntries085 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (-1))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq085 (n : Nat) :
    nestingProjection085.numerator[n]! = nestingEntries085 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries085, if_neg (by omega : ¬ n < 64)]

def nestingProjection086 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1]⟩
theorem nestingLookup086 : projections[86]! = nestingProjection086 := by
  rw [projections_lookup]
  rfl
def nestingEntries086 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq086 (n : Nat) :
    nestingProjection086.numerator[n]! = nestingEntries086 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries086, if_neg (by omega : ¬ n < 64)]

def nestingProjection087 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1]⟩
theorem nestingLookup087 : projections[87]! = nestingProjection087 := by
  rw [projections_lookup]
  rfl
def nestingEntries087 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq087 (n : Nat) :
    nestingProjection087.numerator[n]! = nestingEntries087 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries087, if_neg (by omega : ¬ n < 64)]

def nestingProjection088 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1]⟩
theorem nestingLookup088 : projections[88]! = nestingProjection088 := by
  rw [projections_lookup]
  rfl
def nestingEntries088 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq088 (n : Nat) :
    nestingProjection088.numerator[n]! = nestingEntries088 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries088, if_neg (by omega : ¬ n < 64)]

def nestingProjection089 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1]⟩
theorem nestingLookup089 : projections[89]! = nestingProjection089 := by
  rw [projections_lookup]
  rfl
def nestingEntries089 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else 1)))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq089 (n : Nat) :
    nestingProjection089.numerator[n]! = nestingEntries089 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries089, if_neg (by omega : ¬ n < 64)]

def nestingProjection090 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup090 : projections[90]! = nestingProjection090 := by
  rw [projections_lookup]
  rfl
def nestingEntries090 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq090 (n : Nat) :
    nestingProjection090.numerator[n]! = nestingEntries090 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries090, if_neg (by omega : ¬ n < 64)]

def nestingProjection091 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,-1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup091 : projections[91]! = nestingProjection091 := by
  rw [projections_lookup]
  rfl
def nestingEntries091 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq091 (n : Nat) :
    nestingProjection091.numerator[n]! = nestingEntries091 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries091, if_neg (by omega : ¬ n < 64)]

def nestingProjection092 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,1,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,1,-1,0,0,0,0,1,1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup092 : projections[92]! = nestingProjection092 := by
  rw [projections_lookup]
  rfl
def nestingEntries092 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq092 (n : Nat) :
    nestingProjection092.numerator[n]! = nestingEntries092 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries092, if_neg (by omega : ¬ n < 64)]

def nestingProjection093 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,-1,0,0,0,0,1,1,-1,-1,0,0,0,0,-1,-1,1,1,0,0,0,0,-1,-1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup093 : projections[93]! = nestingProjection093 := by
  rw [projections_lookup]
  rfl
def nestingEntries093 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq093 (n : Nat) :
    nestingProjection093.numerator[n]! = nestingEntries093 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries093, if_neg (by omega : ¬ n < 64)]

def nestingProjection094 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,1,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup094 : projections[94]! = nestingProjection094 := by
  rw [projections_lookup]
  rfl
def nestingEntries094 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq094 (n : Nat) :
    nestingProjection094.numerator[n]! = nestingEntries094 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries094, if_neg (by omega : ¬ n < 64)]

def nestingProjection095 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,1,-1,1,-1,0,0,0,0,-1,1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup095 : projections[95]! = nestingProjection095 := by
  rw [projections_lookup]
  rfl
def nestingEntries095 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq095 (n : Nat) :
    nestingProjection095.numerator[n]! = nestingEntries095 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries095, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection096 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup096 : projections[96]! = nestingProjection096 := by
  rw [projections_lookup]
  rfl
def nestingEntries096 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq096 (n : Nat) :
    nestingProjection096.numerator[n]! = nestingEntries096 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries096, if_neg (by omega : ¬ n < 64)]

def nestingProjection097 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,-1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup097 : projections[97]! = nestingProjection097 := by
  rw [projections_lookup]
  rfl
def nestingEntries097 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then 1 else 0))) else 0)) else 0
theorem nestingEntries_eq097 (n : Nat) :
    nestingProjection097.numerator[n]! = nestingEntries097 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries097, if_neg (by omega : ¬ n < 64)]

def nestingProjection098 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1]⟩
theorem nestingLookup098 : projections[98]! = nestingProjection098 := by
  rw [projections_lookup]
  rfl
def nestingEntries098 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq098 (n : Nat) :
    nestingProjection098.numerator[n]! = nestingEntries098 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries098, if_neg (by omega : ¬ n < 64)]

def nestingProjection099 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,-1,0,1]⟩
theorem nestingLookup099 : projections[99]! = nestingProjection099 := by
  rw [projections_lookup]
  rfl
def nestingEntries099 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq099 (n : Nat) :
    nestingProjection099.numerator[n]! = nestingEntries099 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries099, if_neg (by omega : ¬ n < 64)]

def nestingProjection100 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1]⟩
theorem nestingLookup100 : projections[100]! = nestingProjection100 := by
  rw [projections_lookup]
  rfl
def nestingEntries100 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq100 (n : Nat) :
    nestingProjection100.numerator[n]! = nestingEntries100 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries100, if_neg (by omega : ¬ n < 64)]

def nestingProjection101 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1]⟩
theorem nestingLookup101 : projections[101]! = nestingProjection101 := by
  rw [projections_lookup]
  rfl
def nestingEntries101 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else (-1))))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq101 (n : Nat) :
    nestingProjection101.numerator[n]! = nestingEntries101 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries101, if_neg (by omega : ¬ n < 64)]

def nestingProjection102 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1]⟩
theorem nestingLookup102 : projections[102]! = nestingProjection102 := by
  rw [projections_lookup]
  rfl
def nestingEntries102 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq102 (n : Nat) :
    nestingProjection102.numerator[n]! = nestingEntries102 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries102, if_neg (by omega : ¬ n < 64)]

def nestingProjection103 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1]⟩
theorem nestingLookup103 : projections[103]! = nestingProjection103 := by
  rw [projections_lookup]
  rfl
def nestingEntries103 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq103 (n : Nat) :
    nestingProjection103.numerator[n]! = nestingEntries103 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries103, if_neg (by omega : ¬ n < 64)]

def nestingProjection104 : Projection := ⟨4,1,#[0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,0,1]⟩
theorem nestingLookup104 : projections[104]! = nestingProjection104 := by
  rw [projections_lookup]
  rfl
def nestingEntries104 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq104 (n : Nat) :
    nestingProjection104.numerator[n]! = nestingEntries104 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries104, if_neg (by omega : ¬ n < 64)]

def nestingProjection105 : Projection := ⟨4,1,#[1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup105 : projections[105]! = nestingProjection105 := by
  rw [projections_lookup]
  rfl
def nestingEntries105 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq105 (n : Nat) :
    nestingProjection105.numerator[n]! = nestingEntries105 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries105, if_neg (by omega : ¬ n < 64)]

def nestingProjection106 : Projection := ⟨4,1,#[1,0,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup106 : projections[106]! = nestingProjection106 := by
  rw [projections_lookup]
  rfl
def nestingEntries106 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq106 (n : Nat) :
    nestingProjection106.numerator[n]! = nestingEntries106 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries106, if_neg (by omega : ¬ n < 64)]

def nestingProjection107 : Projection := ⟨4,1,#[1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,-1,0,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup107 : projections[107]! = nestingProjection107 := by
  rw [projections_lookup]
  rfl
def nestingEntries107 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq107 (n : Nat) :
    nestingProjection107.numerator[n]! = nestingEntries107 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries107, if_neg (by omega : ¬ n < 64)]

def nestingProjection108 : Projection := ⟨4,1,#[1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup108 : projections[108]! = nestingProjection108 := by
  rw [projections_lookup]
  rfl
def nestingEntries108 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq108 (n : Nat) :
    nestingProjection108.numerator[n]! = nestingEntries108 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries108, if_neg (by omega : ¬ n < 64)]

def nestingProjection109 : Projection := ⟨4,1,#[1,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,1,1,0,1,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup109 : projections[109]! = nestingProjection109 := by
  rw [projections_lookup]
  rfl
def nestingEntries109 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq109 (n : Nat) :
    nestingProjection109.numerator[n]! = nestingEntries109 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries109, if_neg (by omega : ¬ n < 64)]

def nestingProjection110 : Projection := ⟨4,1,#[1,0,0,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,1,-1,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup110 : projections[110]! = nestingProjection110 := by
  rw [projections_lookup]
  rfl
def nestingEntries110 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq110 (n : Nat) :
    nestingProjection110.numerator[n]! = nestingEntries110 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries110, if_neg (by omega : ¬ n < 64)]

def nestingProjection111 : Projection := ⟨4,1,#[1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,-1,0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup111 : projections[111]! = nestingProjection111 := by
  rw [projections_lookup]
  rfl
def nestingEntries111 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq111 (n : Nat) :
    nestingProjection111.numerator[n]! = nestingEntries111 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries111, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection112 : Projection := ⟨4,1,#[1,0,0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,1,0,-1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup112 : projections[112]! = nestingProjection112 := by
  rw [projections_lookup]
  rfl
def nestingEntries112 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq112 (n : Nat) :
    nestingProjection112.numerator[n]! = nestingEntries112 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries112, if_neg (by omega : ¬ n < 64)]

def nestingProjection113 : Projection := ⟨1,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup113 : projections[113]! = nestingProjection113 := by
  rw [projections_lookup]
  rfl
def nestingEntries113 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq113 (n : Nat) :
    nestingProjection113.numerator[n]! = nestingEntries113 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries113, if_neg (by omega : ¬ n < 64)]

def nestingProjection114 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,-1,0,0,1]⟩
theorem nestingLookup114 : projections[114]! = nestingProjection114 := by
  rw [projections_lookup]
  rfl
def nestingEntries114 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq114 (n : Nat) :
    nestingProjection114.numerator[n]! = nestingEntries114 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries114, if_neg (by omega : ¬ n < 64)]

def nestingProjection115 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,-1,0,0,1]⟩
theorem nestingLookup115 : projections[115]! = nestingProjection115 := by
  rw [projections_lookup]
  rfl
def nestingEntries115 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq115 (n : Nat) :
    nestingProjection115.numerator[n]! = nestingEntries115 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries115, if_neg (by omega : ¬ n < 64)]

def nestingProjection116 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,-1,0,1,1,0,1,2,0,-1,0,1,1,0,-1,0,2,1,0,0,0,0,-1,-1,1,1]⟩
theorem nestingLookup116 : projections[116]! = nestingProjection116 := by
  rw [projections_lookup]
  rfl
def nestingEntries116 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (-1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (-1) else 1))))) else 0
theorem nestingEntries_eq116 (n : Nat) :
    nestingProjection116.numerator[n]! = nestingEntries116 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries116, if_neg (by omega : ¬ n < 64)]

def nestingProjection117 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,-1,0,1,1,0,-1,2,0,1,0,1,1,0,1,0,2,-1,0,0,0,0,-1,1,-1,1]⟩
theorem nestingLookup117 : projections[117]! = nestingProjection117 := by
  rw [projections_lookup]
  rfl
def nestingEntries117 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (if n < 39 then 1 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq117 (n : Nat) :
    nestingProjection117.numerator[n]! = nestingEntries117 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries117, if_neg (by omega : ¬ n < 64)]

def nestingProjection118 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup118 : projections[118]! = nestingProjection118 := by
  rw [projections_lookup]
  rfl
def nestingEntries118 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq118 (n : Nat) :
    nestingProjection118.numerator[n]! = nestingEntries118 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries118, if_neg (by omega : ¬ n < 64)]

def nestingProjection119 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup119 : projections[119]! = nestingProjection119 := by
  rw [projections_lookup]
  rfl
def nestingEntries119 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq119 (n : Nat) :
    nestingProjection119.numerator[n]! = nestingEntries119 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries119, if_neg (by omega : ¬ n < 64)]

def nestingProjection120 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,-1,0,1,1,0,1,2,0,-1,0,-1,-1,0,1,0,2,-1,0,0,0,0,-1,-1,-1,1]⟩
theorem nestingLookup120 : projections[120]! = nestingProjection120 := by
  rw [projections_lookup]
  rfl
def nestingEntries120 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then 1 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq120 (n : Nat) :
    nestingProjection120.numerator[n]! = nestingEntries120 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries120, if_neg (by omega : ¬ n < 64)]

def nestingProjection121 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,-1,0,1,1,0,-1,2,0,1,0,-1,-1,0,-1,0,2,1,0,0,0,0,-1,1,1,1]⟩
theorem nestingLookup121 : projections[121]! = nestingProjection121 := by
  rw [projections_lookup]
  rfl
def nestingEntries121 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (-1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else 1))))) else 0
theorem nestingEntries_eq121 (n : Nat) :
    nestingProjection121.numerator[n]! = nestingEntries121 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries121, if_neg (by omega : ¬ n < 64)]

def nestingProjection122 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,-1,0,-1,-1,0,1,2,0,-1,0,1,1,0,1,0,2,-1,0,0,0,0,-1,-1,-1,1]⟩
theorem nestingLookup122 : projections[122]! = nestingProjection122 := by
  rw [projections_lookup]
  rfl
def nestingEntries122 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then 1 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq122 (n : Nat) :
    nestingProjection122.numerator[n]! = nestingEntries122 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries122, if_neg (by omega : ¬ n < 64)]

def nestingProjection123 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,-1,0,-1,-1,0,-1,2,0,1,0,1,1,0,-1,0,2,1,0,0,0,0,-1,1,1,1]⟩
theorem nestingLookup123 : projections[123]! = nestingProjection123 := by
  rw [projections_lookup]
  rfl
def nestingEntries123 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (-1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else 1))))) else 0
theorem nestingEntries_eq123 (n : Nat) :
    nestingProjection123.numerator[n]! = nestingEntries123 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries123, if_neg (by omega : ¬ n < 64)]

def nestingProjection124 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup124 : projections[124]! = nestingProjection124 := by
  rw [projections_lookup]
  rfl
def nestingEntries124 (n : Nat) : Int := if n < 64 then (if n < 32 then 0 else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq124 (n : Nat) :
    nestingProjection124.numerator[n]! = nestingEntries124 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries124, if_neg (by omega : ¬ n < 64)]

def nestingProjection125 : Projection := ⟨1,2,#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup125 : projections[125]! = nestingProjection125 := by
  rw [projections_lookup]
  rfl
def nestingEntries125 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq125 (n : Nat) :
    nestingProjection125.numerator[n]! = nestingEntries125 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries125, if_neg (by omega : ¬ n < 64)]

def nestingProjection126 : Projection := ⟨4,2,#[4,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,0,-1,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1]⟩
theorem nestingLookup126 : projections[126]! = nestingProjection126 := by
  rw [projections_lookup]
  rfl
def nestingEntries126 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq126 (n : Nat) :
    nestingProjection126.numerator[n]! = nestingEntries126 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries126, if_neg (by omega : ¬ n < 64)]

def nestingProjection127 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,0,-1,0,0,0,4,0,0,0,0,0,1,-1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,0,1]⟩
theorem nestingLookup127 : projections[127]! = nestingProjection127 := by
  rw [projections_lookup]
  rfl
def nestingEntries127 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq127 (n : Nat) :
    nestingProjection127.numerator[n]! = nestingEntries127 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries127, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths


