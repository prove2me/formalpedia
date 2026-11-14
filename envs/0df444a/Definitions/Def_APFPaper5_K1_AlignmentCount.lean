-- Prove2me | Definitions.Def_APFPaper5_K1_AlignmentCount
-- name    : APFPaper5_K1_AlignmentCount
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:17.6652+00:00
-- url     : https://prove2.me/theorems/cb53138f-ea23-4bad-af1b-ff2b61497e49
-- title:
--   Agreement, opposition, and overlap of Boolean assignments
-- statement:
--   Defines the signs of Boolean sides and the agreement, opposition, and signed overlap sums on a finite family. Assignments of sides are model records. They are not B06 OriginalAlignment values: B06 carries active true tasks, while these functions assign either side to each index.
--
--   **Meaning and scope.** Defines the signs of Boolean sides and the agreement, opposition, and signed overlap sums on a finite family. Fidelity exposure: Assignments of sides are model records. They are not B06 OriginalAlignment values: B06 carries active true tasks, while these functions assign either side to each index.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. Assignments of sides are model records. They are not B06 OriginalAlignment values: B06 carries active true tasks, while these functions assign either side to each index.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_AlignmentCount.lean; Sib v44 / pullbacks v1, SHA-256 01a69c1be4311d9050cc8d1a3c31402e36ab13138b81a75e851e682bd4da142c. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '1617-1657,3034-3075; K clauses remain supplied physical obligations'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_AlignmentCount
title: Counting two alignments of one family of distinctions: the side of each distinction, the overlap, and the numbers of agreements and oppositions
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-13 17:53 HST ("Yes, record is an alignment of distinctions"), on the
 question whether a counted record is held on a side. FOUNDATION_INPUTS B02 (every distinction takes both
 values). Thm_APFPaper5_K1_oriented_count.
standing: definitions for a supplied MODEL of that ruling: an alignment of a family gives each distinction
 of the family one of its two sides.
statement: side b is 1 for one side and -1 for the other. For two alignments v and w of a family S,
 overlapOn S v w is the sum over S of the products of the sides; agreeOn S v w is the number of distinctions
 of S on which the two take the same side; opposeOn S v w is the number on which they take opposite sides.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace APFPaper5.K1

/-- The side of a distinction, as a sign. -/
def side (b : Bool) : ℝ := if b then 1 else -1

/-- The sum over the family of the products of the two sides. -/
def overlapOn {D : Type*} (S : Finset D) (v w : D → Bool) : ℝ := ∑ d ∈ S, side (v d) * side (w d)

/-- The number of distinctions of the family on which the two alignments take the same side: one for each
such distinction, summed over the family. -/
def agreeOn {D : Type*} (S : Finset D) (v w : D → Bool) : ℝ := ∑ d ∈ S, if v d = w d then 1 else 0

/-- The number of distinctions of the family on which the two alignments take opposite sides. -/
def opposeOn {D : Type*} (S : Finset D) (v w : D → Bool) : ℝ := ∑ d ∈ S, if v d = w d then 0 else 1

end APFPaper5.K1


