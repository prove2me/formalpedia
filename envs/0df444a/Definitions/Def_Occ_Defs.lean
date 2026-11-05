-- Prove2me | Definitions.Def_Occ_Defs
-- name    : Occ_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:22:18.009799+00:00
-- url     : https://prove2.me/theorems/486ded31-6f33-4352-9b5f-44741776d67c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_CountKSat_Defs
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_PolyT
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Occ
open Groundwork Groundwork.Prog CountKSat
def Below (n : ℕ) (Φ : Fml) : Prop := ∀ C ∈ Φ, ∀ l ∈ C, l.1 < n
def numOcc (Φ : Fml) : ℕ := (Eight.occurring Φ).card
def StNumOccLe : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → numOcc Φ ≤ n
def StCountOcc : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → cntN n Φ = Eight.numSat Φ * 2 ^ (n - numOcc Φ)
def StCountNil : Prop := ∀ n : ℕ, cntN n [] = 2 ^ n
def StCountAllOccur : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → (∀ i < n, ∃ C ∈ Φ, ∃ l ∈ C, l.1 = i) → cntN n Φ = Eight.numSat Φ
def StSameAsFin : Prop := ∀ (N : ℕ) (φ : Sat3.CNF N), numOcc (Decode.toN φ) = MainTheoremForms.numOcc φ ∧ Eight.numSat (Decode.toN φ) = MainTheoremForms.numSatOcc φ
def timesFree (q : (List Unit × Fml) × ℤ) : ℕ := q.2.toNat * 2 ^ (q.1.1.length - numOcc q.1.2)
def StTimesFreeCert : Prop := PolyT timesFree
def StNumOccCert : Prop := PolyT fun Φ : Fml => List.replicate (numOcc Φ) ()
end Occ


