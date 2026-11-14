-- Prove2me | Definitions.Def_APFPaper5_K1_SharedCost
-- name    : APFPaper5_K1_SharedCost
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:09:24.247765+00:00
-- url     : https://prove2.me/theorems/9220f510-64b8-4a9b-a645-18222799ac9e
-- title:
--   The discount from jointly serving two finite families
-- statement:
--   Defines sharedCost(cost,S,T)=cost(S)+cost(T)-cost(S union T). This is the negative of the codebank channel residual; no sign or score interpretation is assumed.
--
--   **Representation and scope.** The sign is the opposite of Delta in delta_calculus.py. This definition is meaningful without claiming a general cost-to-score transfer.
--
--   **Supplied data or hypotheses.** Arbitrary real-valued cost on finite families and decidable equality.
--
--   **Claim boundaries.** sharedCost may be negative; symmetry alone does not give a role-exchange operation or physical reversal.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_SharedCost.lean; Sib v15, SHA-256 a8bc0b4c5b3a1fddc998941b6d23141c563ac34ce43319192cfea7c0df6e96f0. [{'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1772-1792'}, {'path': 'C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py', 'lines_or_section': '1906-2141'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_SharedCost
title: The shared cost of two families: the cost of holding them apart less the cost of holding them together
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Codebank apf/delta_calculus.py: the residual Delta(S1,S2) = kappa(S1 v S2) - kappa(S1) - kappa(S2)
 and check_T_delta_JR_derived (Delta = eps * (J - R)); apf/core.py check_L_irr Step 1. Paper 1 Supplement
 v9.28:1118-1132 and 2834-2842 (shared support and shared setup costs can lower an increment). Archive export
 of 2026-10-02: no definition of this residual found by keyword search.
standing: a DEFINITION on any cost function of families. sharedCost is the negative of the codebank's Delta.
 Applied to the ledger's familyCost it is a number between two families built from ledger cost alone. Whether
 it is the K layer's score off the record-book side has not been ruled by the author.
statement: sharedCost cost S T = cost S + cost T - cost (S ∪ T).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic

set_option autoImplicit false
namespace APFPaper5.K1

universe u
variable {D : Type u} [DecidableEq D]

/-- The cost of holding two families apart, less the cost of holding them together. -/
def sharedCost (cost : Finset D → ℝ) (S T : Finset D) : ℝ := cost S + cost T - cost (S ∪ T)

end APFPaper5.K1


