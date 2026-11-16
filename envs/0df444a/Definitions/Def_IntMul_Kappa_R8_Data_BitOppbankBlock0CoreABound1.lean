-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:24:14.18273+00:00
-- url     : https://prove2.me/theorems/fc1ab401-5d31-4398-8e01-ac3e3e1f33ca
-- title:
--   Block-0 prefix and copy-out MovesV bounds
-- statement:
--   # Block-0 prefix and copy-out MovesV bounds
--
--   Bounds and `MovesV` certificates for the generator on the concrete prefix `preF` from `initR`, and for the subsequent copy-out sequence `copyoND`. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1 split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
Bounds for `genF initR preF` and the subsequent `copyoND` prefix. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem preF_initR_bounds :
    MovesV (genF initR preF).2 ∧
      ∀ x, (genF initR preF).1 x < SupG.codeBound :=
  genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)

theorem copyoND_from_preF :
    MovesV (genF (genF initR preF).1 copyoND).2 ∧
      ∀ x, (genF (genF initR preF).1 copyoND).1 x < SupG.codeBound :=
  MovesV_copyoND_from (genF initR preF).1
    (fun t ht => preF_wS t ht)
    (fun t ht => preF_wX t ht)
    preF_initR_bounds.2


