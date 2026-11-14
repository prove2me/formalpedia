-- Prove2me | Definitions.Def_APFPaper5_K1_PairNumbers
-- name    : APFPaper5_K1_PairNumbers
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:08:32.168207+00:00
-- url     : https://prove2.me/theorems/88ab3527-ffec-4cf4-a0b6-1ce2063ff44d
-- title:
--   NUMBERS in both orders as a conditional algebraic predicate
-- statement:
--   PairNumbers(p,c) requires p_i p_j p_i = c_ij p_i for every ordered pair in a supplied real algebra. Existence, nonzero marks, repeatability and bounds are separate conditions.
--
--   **Representation and scope.** Matches the author-approved both-orders NUMBERS encoding. It adopts no foundation input and contains no separate SYMMETRY hypothesis.
--
--   **Supplied data or hypotheses.** Ring A with a real algebra structure; families p and c. The predicate quantifies all i,j; it does not itself assert p_i is nonzero or idempotent.
--
--   **Claim boundaries.** The predicate does not supply an occupied interface or identify the numbers with physical cost.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_PairNumbers.lean; Sib v15, SHA-256 6b5d3bc8a000f91b69c8d7584b38588f14f4012b87c72220bb1d599817f14e47. [{'path': 'Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_symmetry_retired_2026-11-12.md', 'lines_or_section': '1-2; not settled'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '3038-3041'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_PairNumbers
title: The numbers hypothesis in both orders: every ordered pair of marks has a number
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's ruling of 2026-11-12 ("Yes" to: retire symmetry as a separate hypothesis and state the
 numbers hypothesis in both orders). Paper 5 Supplement v7.33:3037-3040 (K1).
standing: a NAMED HYPOTHESIS of the K layer (NUMBERS), off the record-book side. It is not a declared input
 and no declared input produces it. A derivation is owed. On the record-book side the score is the adopted
 shared count (Def_APFPaper5_K1_SharedCount), not this predicate.
statement: PairNumbers p c says that for every ordered pair of marks the three-letter word p i, p j, p i is
 c i j times p i. Both orders are included because i and j range over all pairs.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs

set_option autoImplicit false
namespace APFPaper5.K1

universe u uA
variable {ι : Type u} {A : Type uA} [Ring A] [Algebra ℝ A]

/-- Every ordered pair of marks has a number. -/
def PairNumbers (p : ι → A) (c : ι → ι → ℝ) : Prop :=
  ∀ i j, p i * p j * p i = c i j • p i

end APFPaper5.K1


