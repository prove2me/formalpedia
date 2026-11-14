-- Prove2me | Definitions.Def_APFPaper5_K4_TwoSheets
-- name    : APFPaper5_K4_TwoSheets
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:53:36.846624+00:00
-- url     : https://prove2.me/theorems/80882bc4-db8f-4414-beb7-025df9c17ddb
-- title:
--   A supplied two-sheet composite
-- statement:
--   Defines a direct pair of joint carriers, product and conjugated product, independent part turns, co-turn and sheetwise record readings. This is an explicit alternative model. Its sheets and mirror products are not an independently constructed physical orientation cover.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: This is an explicit alternative model. Its sheets and mirror products are not an independently constructed physical orientation cover.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K4.jointZero', 'statement_and_binders': 'def jointZero : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointNeg', 'statement_and_binders': 'def jointNeg (p : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointTurn', 'statement_and_binders': 'def jointTurn (c s : ℝ) (p : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointCost', 'statement_and_binders': 'def jointCost (p : Joint) : ℝ'}
--   - {'declaration': 'APFPaper5.K4.pairAnti', 'statement_and_binders': 'def pairAnti (h k : Held2) : Joint'}
--   - {'declaration': 'APFPaper5.K4.Sheets', 'statement_and_binders': '@[ext] structure Sheets'}
--   - {'declaration': 'APFPaper5.K4.sheetsPair', 'statement_and_binders': 'def sheetsPair (h k : Held2) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.turnFirstBy', 'statement_and_binders': 'def turnFirstBy (c s : ℝ) (p : Sheets) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.turnSecondBy', 'statement_and_binders': 'def turnSecondBy (c s : ℝ) (p : Sheets) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.coTurn', 'statement_and_binders': 'def coTurn (C S : ℝ) (p : Sheets) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.sheetsAdd', 'statement_and_binders': 'def sheetsAdd (p q : Sheets) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.sheetsSmul', 'statement_and_binders': 'def sheetsSmul (r : ℝ) (p : Sheets) : Sheets'}
--   - {'declaration': 'APFPaper5.K4.sheetsReading', 'statement_and_binders': "def sheetsReading (w w' : RecordWeights) (p : Sheets) : ℝ"}
--   - {'declaration': 'APFPaper5.K4.transposeSecond', 'statement_and_binders': 'def transposeSecond (w : RecordWeights) : RecordWeights'}
--
--   **Limits**
--
--   - Q44-01
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K4_TwoSheets.lean; Sib v44 / pullbacks v1, SHA-256 8a492a3ddce516148315cd5395f9d53d8baeb27d6b47b69568cceab259c9876d. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2058-2090,2213-2235'}; {'path': 'source/Definitions/Def_APFPaper5_K4_TwoSheets.lean', 'sha256': '8a492a3ddce516148315cd5395f9d53d8baeb27d6b47b69568cceab259c9876d'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_TwoSheets
title: A joint carrier with no shared quarter turn put in: two sheets, the mirror product, turns of each part, and the turn of both parts together
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:2058-2090 (Q4B: orientation-preserving and orientation-reversing embeddings;
 sign synchronization), 2213-2219 (orientation synchronization is load bearing; without it the domain is not
 the complex tensor product). Codebank graded_orientation_closure.py
 (check_T_orientation_parity_cocycle_criterion, check_T_double_cover_always_orients).
standing: a supplied MODEL. Nothing here is a declared input.
statement: jointZero, jointNeg, jointTurn and jointCost are the zero joint state, the reversal of every
 entry, the common turn of every joint component, and the sum of the four costs. pairAnti h k is the joint
 state of h with k read with its rates reversed: the mirror product. Sheets is a pair of joint states, one
 on each sheet. sheetsPair h k puts the product on the first sheet and the mirror product on the second.
 turnFirstBy and turnSecondBy turn the first part and the second part: they agree on the first sheet and
 are opposite on the second. coTurn C S is what turning both parts together does: a turn of the first
 sheet and nothing on the second. sheetsReading w w' reads the first sheet's record book with weights w
 and the second's with weights w'. transposeSecond w is the set of weights that reads on a product what
 w reads on the mirror product.
-/
import Definitions.Def_APFPaper5_K4_JointCarrier
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

/-- The zero joint state. -/
def jointZero : Joint := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Every entry reversed. -/
def jointNeg (p : Joint) : Joint := ⟨-p.x1, -p.y1, -p.x2, -p.y2, -p.x3, -p.y3, -p.x4, -p.y4⟩

/-- The common turn of every joint component. -/
def jointTurn (c s : ℝ) (p : Joint) : Joint :=
  ⟨c * p.x1 - s * p.y1, s * p.x1 + c * p.y1, c * p.x2 - s * p.y2, s * p.x2 + c * p.y2,
   c * p.x3 - s * p.y3, s * p.x3 + c * p.y3, c * p.x4 - s * p.y4, s * p.x4 + c * p.y4⟩

/-- The sum of the four costs of a joint state. -/
def jointCost (p : Joint) : ℝ :=
  p.x1 * p.x1 + p.y1 * p.y1 + p.x2 * p.x2 + p.y2 * p.y2 + p.x3 * p.x3 + p.y3 * p.y3 + p.x4 * p.x4 +
    p.y4 * p.y4

/-- The mirror product: the second state read with its rates reversed. -/
def pairAnti (h k : Held2) : Joint := pair h (rateFlip k)

/-- A joint state on each of two sheets. -/
@[ext] structure Sheets where
  sync : Joint
  anti : Joint

/-- The product on the first sheet and the mirror product on the second. -/
def sheetsPair (h k : Held2) : Sheets := ⟨pair h k, pairAnti h k⟩

/-- A turn of the first part. -/
def turnFirstBy (c s : ℝ) (p : Sheets) : Sheets := ⟨jointTurn c s p.sync, jointTurn c s p.anti⟩

/-- A turn of the second part: the same on the first sheet, the opposite on the second. -/
def turnSecondBy (c s : ℝ) (p : Sheets) : Sheets := ⟨jointTurn c s p.sync, jointTurn c (-s) p.anti⟩

/-- What turning both parts together does: a turn of the first sheet, nothing on the second. -/
def coTurn (C S : ℝ) (p : Sheets) : Sheets := ⟨jointTurn C S p.sync, p.anti⟩

/-- Sheetwise sum. -/
def sheetsAdd (p q : Sheets) : Sheets := ⟨jointAdd p.sync q.sync, jointAdd p.anti q.anti⟩

/-- Sheetwise scaling. -/
def sheetsSmul (r : ℝ) (p : Sheets) : Sheets := ⟨jointSmul r p.sync, jointSmul r p.anti⟩

/-- A reading of both record books. -/
def sheetsReading (w w' : RecordWeights) (p : Sheets) : ℝ :=
  linearRecord w p.sync + linearRecord w' p.anti

/-- The weights that read, on a product, what `w` reads on the mirror product. -/
def transposeSecond (w : RecordWeights) : RecordWeights :=
  ⟨w.d1, w.d2, w.d3, w.d4, w.u12, -w.v12, w.u13, w.v13, w.u23, w.v23, w.u14, w.v14, w.u24, w.v24,
   w.u34, -w.v34⟩

end APFPaper5.K4


