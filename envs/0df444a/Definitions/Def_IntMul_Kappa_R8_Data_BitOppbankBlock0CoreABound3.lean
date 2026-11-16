-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:29:25.521967+00:00
-- url     : https://prove2.me/theorems/c76a15ab-989c-45b7-a971-e41034b03ad5
-- title:
--   Block-0 copy-out plus leaf-mix bounds from the prefix
-- statement:
--   # Block-0 copy-out plus leaf-mix bounds from the prefix
--
--   Combined bounds for appending `copyoND` and `leafMix` after the prefix, using `genF_append_fst` on `(genF initR preF).1` as a unit. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3 split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
Bounds for `copyoND ++ leafMix` after `preF`, via abstract `genF_append_fst`. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem copyoND_leafMix_from_preF :
    MovesV (genF (genF initR preF).1 (copyoND ++ leafMix)).2 ∧
      ∀ x, (genF (genF initR preF).1 (copyoND ++ leafMix)).1 x <
        SupG.codeBound := by
  have hfst := genF_append_fst (genF initR preF).1 copyoND leafMix
  have hsnd := congrArg Prod.snd (genF_append (genF initR preF).1 copyoND leafMix)
  refine ⟨?_, ?_⟩
  · rw [hsnd]; exact MovesV_append.2 ⟨copyoND_from_preF.1, leafMix_from_f2.1⟩
  · intro x
    have : (genF (genF initR preF).1 (copyoND ++ leafMix)).1 x =
        (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 x := by
      rw [hfst]
    rw [this]
    exact leafMix_from_f2.2 x


