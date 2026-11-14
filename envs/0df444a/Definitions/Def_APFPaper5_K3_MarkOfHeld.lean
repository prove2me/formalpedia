-- Prove2me | Definitions.Def_APFPaper5_K3_MarkOfHeld
-- name    : APFPaper5_K3_MarkOfHeld
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:52:29.280299+00:00
-- url     : https://prove2.me/theorems/d55cd5a9-5878-46ae-8462-9896fd14f281
-- title:
--   Mark coordinates and overlap on a supplied carrier
-- statement:
--   Defines the three-coordinate quadratic mark map and squared complex-overlap expression on Held2. The V3 target is supplied mathematical data, not derived spatial dimension or a physical Born probability.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: The V3 target is supplied mathematical data, not derived spatial dimension or a physical Born probability.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K3.markDirection', 'statement_and_binders': 'def markDirection (h : Held2) : V3'}
--   - {'declaration': 'APFPaper5.K3.overlap', 'statement_and_binders': 'def overlap (h k : Held2) : ℝ'}
--
--   **Limits**
--
--   - Q44-01
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_MarkOfHeld.lean; Sib v44 / pullbacks v1, SHA-256 b6a1b96b8ca14ed7daa49b37fb630bc21d529373921d1f4e2262567dbe2a43f0. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717,3034-3076'}; {'path': 'source/Definitions/Def_APFPaper5_K3_MarkOfHeld.lean', 'sha256': 'b6a1b96b8ca14ed7daa49b37fb630bc21d529373921d1f4e2262567dbe2a43f0'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_MarkOfHeld
title: The direction of a held state in the three-direction mark space, and the number between two held states
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K3_ThreeDirections; Thm_APFPaper5_K1_rank_three (the score between a mark and its turn is
 (1 + x) / 2). Paper 5 Supplement v7.33:40-52 and 3037-3040 (K1).
standing: part of the supplied MODEL of two held components.
statement: markDirection h is the triple: twice the first cross term, twice the second cross term, and the
 cost of the first component minus the cost of the second. overlap h k is the square of the cross term of
 cost between h and k plus the square of the cross term between h and the quarter turn of k.
-/
import Definitions.Def_APFPaper5_K3_ThreeDirections
import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents

set_option autoImplicit false
namespace APFPaper5.K3

/-- The direction of a held state in the three-direction mark space. -/
def markDirection (h : Held2) : V3 := ⟨2 * crossRe h, 2 * crossIm h, recA h - recB h⟩

/-- The number between two held states, before dividing by their costs. -/
def overlap (h k : Held2) : ℝ :=
  (h.a1 * k.a1 + h.a2 * k.a2 + h.b1 * k.b1 + h.b2 * k.b2) *
      (h.a1 * k.a1 + h.a2 * k.a2 + h.b1 * k.b1 + h.b2 * k.b2) +
    (h.a2 * k.a1 - h.a1 * k.a2 + h.b2 * k.b1 - h.b1 * k.b2) *
      (h.a2 * k.a1 - h.a1 * k.a2 + h.b2 * k.b1 - h.b1 * k.b2)

end APFPaper5.K3


