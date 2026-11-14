-- Prove2me | Definitions.Def_APFPaper5_K1_RegionSymmetries
-- name    : APFPaper5_K1_RegionSymmetries
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:15.805137+00:00
-- url     : https://prove2.me/theorems/81fcb7d6-50d2-4a3f-92be-a871aaf3a1a3
-- title:
--   Permutations, side flips, and realization of all Boolean patterns
-- statement:
--   Defines coordinate permutation, side flips, opposition, and the predicate that every assignment is realized by some state; includes a four-coordinate example. AllSidesHeld is a substantive surjectivity hypothesis, stronger than separate two-sidedness of each distinction. It is not B02 or an adopted physical input.
--
--   **Meaning and scope.** Defines coordinate permutation, side flips, opposition, and the predicate that every assignment is realized by some state; includes a four-coordinate example. Fidelity exposure: AllSidesHeld is a substantive surjectivity hypothesis, stronger than separate two-sidedness of each distinction. It is not B02 or an adopted physical input.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. AllSidesHeld is a substantive surjectivity hypothesis, stronger than separate two-sidedness of each distinction. It is not B02 or an adopted physical input.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_RegionSymmetries.lean; Sib v44 / pullbacks v1, SHA-256 531055ce992ba593ce24daf968bc49622f15af8222861d780bd1d76bebdf2b9e. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '1617-1657,3034-3075; K clauses remain supplied physical obligations'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_RegionSymmetries
title: Rearranging the distinctions of a region, reading distinctions the other way, the opposite alignment, the statement that every combination of sides is held by some potential state, and a four-distinction example
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statements of 2026-11-13 18:19 HST ("This is just a permutation of the distinctions in a
 region - every combination of sides across a family is held by some POTENTIAL state") and 18:21 HST
 ("Records come in pairs because one mark has no meaning, and two marks bring the distance between. Two marks
 is the minimum"). Def_APFPaper5_K1_AlignmentCount.
standing: definitions for a supplied MODEL of those statements. None is a declared input.
statement: rearrange sigma v is the alignment that holds, at each distinction, the side v holds at the
 distinction sigma sends it to. rename f v reads the distinctions marked by f the other way. opposite v holds
 every distinction on its other side. AllSidesHeld reads says that for every assignment of sides to the family
 some potential state reads that assignment. shift4 moves each of four distinctions to the next, the last to
 the first; twoAndTwo holds the first two on one side and the last two on the other.
-/
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace APFPaper5.K1

/-- The alignment after the distinctions of the region are rearranged by `sigma`. -/
def rearrange {D : Type*} (sigma : D ≃ D) (v : D → Bool) : D → Bool := fun d => v (sigma d)

/-- The alignment with the distinctions marked by `f` read the other way. -/
def rename {D : Type*} (f v : D → Bool) : D → Bool := fun d => xor (f d) (v d)

/-- The alignment with every distinction on its other side. -/
def opposite {D : Type*} (v : D → Bool) : D → Bool := fun d => !(v d)

/-- Every combination of sides across the family is held by some potential state. -/
def AllSidesHeld {X D : Type*} (reads : D → X → Bool) : Prop :=
  ∀ v : D → Bool, ∃ x : X, ∀ d : D, reads d x = v d

/-- Four distinctions, each moved to the next and the last to the first. -/
def shift4 : Fin 4 ≃ Fin 4 where
  toFun i := i + 1
  invFun i := i + 3
  left_inv := by intro i; revert i; decide
  right_inv := by intro i; revert i; decide

/-- The first two of four distinctions on one side, the last two on the other. -/
def twoAndTwo : Fin 4 → Bool := fun i => decide (i.val < 2)

end APFPaper5.K1


