-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5d
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5d
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:40:54.607365+00:00
-- url     : https://prove2.me/theorems/4ec2a841-16fc-4e93-af8b-d3c6c314d0fc
-- title:
--   State transport for the prefix-copy-leaf generator
-- statement:
--   # State transport for the prefix-copy-leaf generator
--
--   Equality between the generator state of the public word `preF ++ copyoND ++ leafMix` and the nested composition `(genF (genF (genF initR preF).1 copyoND).1 leafMix).1`, transported through irreducible aliases. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5d`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5d split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c
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
State transport for `preF ++ copyoND ++ leafMix` via irreducible aliases and abstract `genF_append3_fst`.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem genF_append3_fst_ir :
    (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 =
      (genF (genF (genF initR preF_ir).1 copyoND_ir).1 leafMix_ir).1 :=
  genF_append3_fst initR preF_ir copyoND_ir leafMix_ir

theorem genF_preF_copyoND_leafMix_word_eq :
    preF ++ copyoND ++ leafMix = preF_ir ++ copyoND_ir ++ leafMix_ir := by
  have e_pre : preF ++ copyoND_ir ++ leafMix_ir =
      preF_ir ++ copyoND_ir ++ leafMix_ir :=
    congrArg (fun w => w ++ copyoND_ir ++ leafMix_ir) preF_ir_eq.symm
  have e_copy : preF ++ copyoND ++ leafMix_ir =
      preF ++ copyoND_ir ++ leafMix_ir :=
    congrArg (fun w => preF ++ w ++ leafMix_ir) copyoND_ir_eq.symm
  have e_leaf : preF ++ copyoND ++ leafMix =
      preF ++ copyoND ++ leafMix_ir :=
    congrArg (fun w => preF ++ copyoND ++ w) leafMix_ir_eq.symm
  exact e_leaf.trans (e_copy.trans e_pre)

theorem genF_preF_copyoND_leafMix_state :
    (genF initR (preF ++ copyoND ++ leafMix)).1 =
      (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 := by
  have lhs :
      (genF initR (preF ++ copyoND ++ leafMix)).1 =
        (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 :=
    congrArg (fun W => (genF initR W).1) genF_preF_copyoND_leafMix_word_eq
  have e0 : (genF initR preF).1 = (genF initR preF_ir).1 :=
    congrArg (fun W => (genF initR W).1) preF_ir_eq.symm
  have e1 : (genF (genF initR preF).1 copyoND).1 =
      (genF (genF initR preF_ir).1 copyoND_ir).1 := by
    have hcopy : (genF (genF initR preF).1 copyoND).1 =
        (genF (genF initR preF).1 copyoND_ir).1 :=
      congrArg (fun C => (genF (genF initR preF).1 C).1) copyoND_ir_eq.symm
    have hpre : (genF (genF initR preF).1 copyoND_ir).1 =
        (genF (genF initR preF_ir).1 copyoND_ir).1 :=
      congrArg (fun s => (genF s copyoND_ir).1) e0
    exact hcopy.trans hpre
  have e2 : (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 =
      (genF (genF (genF initR preF_ir).1 copyoND_ir).1 leafMix_ir).1 := by
    have hleaf : (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 =
        (genF (genF (genF initR preF).1 copyoND).1 leafMix_ir).1 :=
      congrArg (fun C => (genF (genF (genF initR preF).1 copyoND).1 C).1) leafMix_ir_eq.symm
    have hprev : (genF (genF (genF initR preF).1 copyoND).1 leafMix_ir).1 =
        (genF (genF (genF initR preF_ir).1 copyoND_ir).1 leafMix_ir).1 :=
      congrArg (fun s => (genF s leafMix_ir).1) e1
    exact hleaf.trans hprev
  exact lhs.trans (genF_append3_fst_ir.trans e2.symm)


