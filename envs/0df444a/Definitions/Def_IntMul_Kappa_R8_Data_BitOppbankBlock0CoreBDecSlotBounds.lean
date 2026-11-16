-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotBounds
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotBounds
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:32:53.264529+00:00
-- url     : https://prove2.me/theorems/fe01d55c-bb12-4cdb-958f-adb4b96f9bda
-- title:
--   Block-0 slot-certificate interval bounds
-- statement:
--   # Block-0 slot-certificate interval bounds
--
--   Each slot-certificate record lies in the source interval of its declared leaf owners. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotBounds`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotBounds split. Prefix / block-0 helper only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 CoreB decide/proof split. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem gateSlotCert_bounds :
    ∀ p ∈ gateSlotCert,
      slotSrcP p ≤ slotPiv p ∧
      slotPiv p < slotHiP p ∧
      slotSrcB p ≤ slotBp1 p ∧
      slotBp1 p < slotHiB p ∧
      slotPiv p < 11099 ∧
      slotBp1 p < 11099 := by
  decide


