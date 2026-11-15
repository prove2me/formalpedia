-- Prove2me | Definitions.Def_APFPaper5_K1_TurnRound
-- name    : APFPaper5_K1_TurnRound
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:26:39.348664+00:00
-- url     : https://prove2.me/theorems/af6162b7-5121-4b30-9119-20993449a884
-- title:
--   Supplied cyclic Boolean shift
-- statement:
--   The map is supplied ordinary mathematics; no input or physical admission is asserted. No project Prop-valued structure field is introduced; holdStep uses Boolean xor and an Equiv with proved inverse laws.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K1.turnRound', 'statement_and_binders': 'def turnRound (m : ℕ) : (Fin (m + 1) → Bool) → Fin (m + 1) → Bool'}
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_TurnRound.lean; Sib v58 / pullbacks v9, SHA-256 58bd37f5df40f99fe6a8138149c79d4e851b72d481e17a091c7b5df6078811cc. {'path': 'source/Definitions/Def_APFPaper5_K1_TurnRound.lean', 'sha256': '58bd37f5df40f99fe6a8138149c79d4e851b72d481e17a091c7b5df6078811cc', 'line': 25, 'declaration': 'APFPaper5.K1.turnRound'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K1_TurnRound
title: The rearrangement that turns a finite region round one place, turning over the one distinction that comes round
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ordinary mathematics on Def_APFPaper5_K1_PairParity (holdStep). The map is a rearrangement with one
 turn-over, so it is of the kind the two readings of a hold adopted on 2026-11-14 11:33 HST
 (RULING_hold_readings_2026-11-14) allow. Paper 5 Supplement v7.33:3559-3564 and 3670-3674 (finite calibration
 certifies only a declared finite-resolution orbit cover) is the statement it is a count-model instance of.
 FOUNDATION_INPUTS is not consumed.
standing: a definition of a map. It is supplied, not derived, and no claim is made here that it is an
 admitted hold of any interface.
contents: turnRound m acts on the records of a region with m + 1 distinctions, numbered 0 to m. Each
 distinction below m comes to read what the next one read. Distinction m comes to read what distinction 0
 read, turned over. On two distinctions (m = 1) it is the quarter turn of the pair.
-/
import Definitions.Def_APFPaper5_K1_PairParity
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
namespace APFPaper5.K1

/-- Turn the region round one place, turning over the one distinction that comes round. -/
def turnRound (m : ℕ) : (Fin (m + 1) → Bool) → Fin (m + 1) → Bool :=
  holdStep (fun j => decide (j.val = m)) (finRotate (m + 1))

end APFPaper5.K1


