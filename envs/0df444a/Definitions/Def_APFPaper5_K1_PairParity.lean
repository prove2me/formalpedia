-- Prove2me | Definitions.Def_APFPaper5_K1_PairParity
-- name    : APFPaper5_K1_PairParity
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:53.837864+00:00
-- url     : https://prove2.me/theorems/54da3749-73fe-4c7d-96e0-174b6eed6d80
-- title:
--   Parity and signed permutations of Boolean records
-- statement:
--   Defines product parity, permutation followed by coordinate flips, the marks held by a record, and an explicit signed swap on two coordinates. The flip mask and permutation are supplied transformations. No physical admission, continuous turn, or cost law follows from these definitions.
--
--   **Meaning and scope.** Defines product parity, permutation followed by coordinate flips, the marks held by a record, and an explicit signed swap on two coordinates. Fidelity exposure: The flip mask and permutation are supplied transformations. No physical admission, continuous turn, or cost law follows from these definitions.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. The flip mask and permutation are supplied transformations. No physical admission, continuous turn, or cost law follows from these definitions.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_PairParity.lean; Sib v44 / pullbacks v1, SHA-256 8a17a59425a646a1afaf3a0274d9c50220a97f591a60b498e7b185151a4f9743. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '1617-1657,3034-3075; K clauses remain supplied physical obligations'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_PairParity
title: The sign of a pair of records (minus one once for each opposition), a hold step made of rearranging and reading the other way, the marks a record holds, and a quarter turn on two distinctions
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's direction of 2026-11-13 18:39 HST ("Derive hold answer"), on the question whether a hold
 may turn a single distinction over. Def_APFPaper5_K1_AlignmentCount. Def_APFPaper5_K1_RegionSymmetries.
standing: definitions for a supplied MODEL. None is a declared input.
statement: pairSign S v w is the product over the family of the products of the two sides: one factor of
 minus one for each distinction on which the two records are opposed. holdStep f sigma x rearranges the
 distinctions of x by sigma and then reads the distinctions marked by f the other way. marksOf v is the set
 of marks the record holds: for each distinction, the side it is held on. swap2 exchanges two distinctions;
 firstOnly marks the first; quarter2 exchanges the two and turns the first over.
-/
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APFPaper5_K1_RegionSymmetries

set_option autoImplicit false
namespace APFPaper5.K1

/-- Minus one once for each distinction of the family on which the two records are opposed. -/
def pairSign {D : Type*} (S : Finset D) (v w : D → Bool) : ℝ := ∏ d ∈ S, side (v d) * side (w d)

/-- Rearrange the distinctions, then read those marked by `f` the other way. -/
def holdStep {D : Type*} (f : D → Bool) (sigma : D ≃ D) (x : D → Bool) : D → Bool :=
  rename f (rearrange sigma x)

/-- The marks a record holds: each distinction together with the side it is held on. -/
def marksOf {D : Type*} (v : D → Bool) : Set (D × Bool) := {m | v m.1 = m.2}

/-- Two distinctions exchanged. -/
def swap2 : Fin 2 ≃ Fin 2 where
  toFun i := i + 1
  invFun i := i + 1
  left_inv := by intro i; revert i; decide
  right_inv := by intro i; revert i; decide

/-- Marks the first of two distinctions. -/
def firstOnly : Fin 2 → Bool := fun i => decide (i.val = 0)

/-- Exchange the two distinctions and turn the first over. -/
def quarter2 (x : Fin 2 → Bool) : Fin 2 → Bool := holdStep firstOnly swap2 x

end APFPaper5.K1


