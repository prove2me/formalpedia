-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner03
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner03
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:32:37.806059+00:00
-- url     : https://prove2.me/theorems/4dfd3a6e-da70-4ce7-9aa2-7ae17d9efbeb
-- title:
--   Block-0 owner-certificate chunk 03 specification
-- statement:
--   # Block-0 owner-certificate chunk 03 specification
--
--   Specification of owner-certificate chunk 03: each record's leaf index is in range and its source/high fields match `srcS_vals`. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner03`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner03 split. Prefix / block-0 helper only; not a full-word W1F certificate.

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

theorem gateOwnerCert_spec_03 :
    ∀ p ∈ gateOwnerCert_c03,
      p.1 < 1771 ∧ srcS_vals[p.1]! = p.2.1 ∧
        (if p.1 + 1 = 1771 then 11099 else srcS_vals[p.1 + 1]!) = p.2.2 := by
  decide


