-- Prove2me | Definitions.Def_APFPaper5_K4_CompositeOnly
-- name    : APFPaper5_K4_CompositeOnly
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:53:36.393931+00:00
-- url     : https://prove2.me/theorems/788d972c-e5a6-48d1-a23f-acf205ebaf1f
-- title:
--   Rate-free states and a composite record
-- statement:
--   Defines RateFree by two zero coordinate entries and a particular joint quadratic-record weighting. Rate means coordinate in this model, not a proved time derivative. Composite record is not an original irreducibly joint distinction.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: Rate means coordinate in this model, not a proved time derivative. Composite record is not an original irreducibly joint distinction.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K4.RateFree', 'statement_and_binders': 'def RateFree (h : Held2) : Prop'}
--   - {'declaration': 'APFPaper5.K4.compositeOnly', 'statement_and_binders': 'def compositeOnly : RecordWeights'}
--
--   **Limits**
--
--   - Q44-01
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K4_CompositeOnly.lean; Sib v44 / pullbacks v1, SHA-256 fc9c7bbc216164a2985193daa3ce49f1a9c727b1c1c249ed36a653b0550d6e40. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2221-2235'}; {'path': 'source/Definitions/Def_APFPaper5_K4_CompositeOnly.lean', 'sha256': 'fc9c7bbc216164a2985193daa3ce49f1a9c727b1c1c249ed36a653b0550d6e40'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_CompositeOnly
title: Held states with no rate, and the joint reading that the parts' records cannot build without one
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:2221-2234 (Q4D: parameter counting is "a necessary check of local tomography
 ... not ... the field selection proof"). Codebank quantum_admissibility.py (check_T_field_selection_complex:
 the composite accounting defect, under the regime "no hidden composite-only record directions"),
 composite_only_direction.py (the surplus identified, with a witness pair), closed_world_completeness.py.
standing: part of the supplied MODEL of composition.
statement: RateFree h says both rates of h are zero. compositeOnly is the set of weights that reads the
 cross term of AA' with BB' minus the cross term of AB' with BA'.
-/
import Definitions.Def_APFPaper5_K4_JointCarrier

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

/-- Both rates are zero. -/
def RateFree (h : Held2) : Prop := h.a2 = 0 ∧ h.b2 = 0

/-- The cross term of AA' with BB' minus the cross term of AB' with BA'. -/
def compositeOnly : RecordWeights := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0⟩

end APFPaper5.K4


