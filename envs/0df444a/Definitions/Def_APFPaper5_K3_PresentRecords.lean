-- Prove2me | Definitions.Def_APFPaper5_K3_PresentRecords
-- name    : APFPaper5_K3_PresentRecords
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:49.879639+00:00
-- url     : https://prove2.me/theorems/2fd76b53-ee10-4e21-9098-59eb2457cedb
-- title:
--   Present model records
-- statement:
--   Defines plainNow as the two component squared costs and their unturned recombination cost. This chosen triple is not the complete physical-fact family or original continuation profile.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: This chosen triple is not the complete physical-fact family or original continuation profile.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K3.plainNow', 'statement_and_binders': 'def plainNow (h : Held2) : ℝ × ℝ × ℝ'}
--
--   **Limits**
--
--   - Q44-01
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_PresentRecords.lean; Sib v44 / pullbacks v1, SHA-256 9f4beefc1278bb91f78ee50a2f0df0b5f4bd0b6bc07c2be95ab7c26c4aedf15f. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}; {'path': 'source/Definitions/Def_APFPaper5_K3_PresentRecords.lean', 'sha256': '9f4beefc1278bb91f78ee50a2f0df0b5f4bd0b6bc07c2be95ab7c26c4aedf15f'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_PresentRecords
title: The present records of two held components: the two costs and the plain recombination
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K3_TwoComponents. Paper 5 Supplement v7.33:1617-1650 ("first-order local completeness
 keeps both present comparison and continuation direction").
standing: part of the supplied MODEL of two held components.
statement: plainNow h is the triple of the cost of the first component, the cost of the second, and the cost
 of the two recombined, read with no turn.
-/
import Definitions.Def_APFPaper5_K3_TwoComponents

set_option autoImplicit false
namespace APFPaper5.K3

/-- The two costs and the plain recombination, read with no turn. -/
def plainNow (h : Held2) : ℝ × ℝ × ℝ := (recA h, recB h, recSum h)

end APFPaper5.K3


