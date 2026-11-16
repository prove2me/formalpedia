-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:39:17.594955+00:00
-- url     : https://prove2.me/theorems/efe7f487-4fc2-4972-8143-2ff38ca65a8a
-- title:
--   Public left-associated prefix-copy-leaf MovesV bounds
-- statement:
--   # Public left-associated prefix-copy-leaf MovesV bounds
--
--   Transport of the left-associated `MovesV` bounds from irreducible aliases onto the public word `preF ++ copyoND ++ leafMix`. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b
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
Left-associated prefix bounds for `preF ++ copyoND ++ leafMix`, transported from irreducible aliases.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem MovesV_preF_copyoND_leaves_bounds :
    MovesV (genF initR (preF ++ copyoND ++ leafMix)).2 ∧
      ∀ x, (genF initR (preF ++ copyoND ++ leafMix)).1 x < SupG.codeBound := by
  have e_pre : preF ++ copyoND_ir ++ leafMix_ir =
      preF_ir ++ copyoND_ir ++ leafMix_ir :=
    congrArg (fun w => w ++ copyoND_ir ++ leafMix_ir) preF_ir_eq.symm
  have e_copy : preF ++ copyoND ++ leafMix_ir =
      preF ++ copyoND_ir ++ leafMix_ir :=
    congrArg (fun w => preF ++ w ++ leafMix_ir) copyoND_ir_eq.symm
  have e_leaf : preF ++ copyoND ++ leafMix =
      preF ++ copyoND ++ leafMix_ir :=
    congrArg (fun w => preF ++ copyoND ++ w) leafMix_ir_eq.symm
  have e := e_leaf.trans (e_copy.trans e_pre)
  have e' :=
    congrArg
      (fun W =>
        MovesV (genF initR W).2 ∧
          ∀ x, (genF initR W).1 x < SupG.codeBound)
      e
  exact e'.mpr MovesV_preF_copyoND_leaves_bounds_ir3


