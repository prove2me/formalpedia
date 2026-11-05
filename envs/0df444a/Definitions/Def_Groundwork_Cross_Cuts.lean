-- Prove2me | Definitions.Def_Groundwork_Cross_Cuts
-- name    : Groundwork_Cross_Cuts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:06.164192+00:00
-- url     : https://prove2.me/theorems/a5dbcabb-d629-4ee5-99d8-1ff7111d18b4
-- title:
--   Cuts
-- statement:
--   Definitions and structural lemmas for Cuts, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
set_option autoImplicit false
section
section
namespace Groundwork
open Finset
structure BitCut where
  top : Bell → Bool → Bool → ℤ
  bot0 : Bell → Bool → Bool → ℤ
  bot1 : Bell → Bool → Bool → ℤ
def BitCut.Top (c : BitCut) {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : ℤ := ∏ k, c.top (β k) (p k) (q k)
def BitCut.Bot (c : BitCut) {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : ℤ :=
  ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
    (∏ k ∈ S, c.bot1 (β k) (p k) (q k)) * ∏ k ∈ Sᶜ, c.bot0 (β k) (p k) (q k)
def ind (a b p q : Bool) : ℤ := if p = a ∧ q = b then 1 else 0
def rowBit : BitCut where
  top h p q := match h with
    | (false, false) => ind false false p q
    | (false, true) => ind true true p q
    | (true, false) => ind true false p q
    | (true, true) => s p q
  bot0 h p q := match h with
    | (false, false) => ind false false p q
    | (false, true) => ind true true p q
    | (true, false) => if p = q then 0 else 1
    | (true, true) => ind false true p q
  bot1 h p q := match h with
    | (true, true) => -s p q
    | _ => 0
def colBit : BitCut where
  top h p q := match h with
    | (false, false) => if p = q then 1 else 0
    | (false, true) => ind true true p q
    | (true, false) => ind false true p q
    | (true, true) => ind true false p q
  bot0 h p q := match h with
    | (false, false) => if p = q then 1 else 0
    | _ => 0
  bot1 h p q := match h with
    | (false, false) => -ind true true p q
    | (false, true) => ind true true p q - ind false false p q
    | (true, false) => ind true false p q
    | (true, true) => ind false true p q
end Groundwork


