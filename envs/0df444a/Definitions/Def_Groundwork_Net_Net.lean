-- Prove2me | Definitions.Def_Groundwork_Net_Net
-- name    : Groundwork_Net_Net
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:45.349881+00:00
-- url     : https://prove2.me/theorems/77850dbb-b17b-421a-bbbd-99abffabbb92
-- title:
--   Net
-- statement:
--   Definitions and structural lemmas for Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
set_option autoImplicit false
section
namespace Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Network
end Network
@[expose] public def Inst.net [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    Network J (J → A) A where
  S v := tuples (fun w => w ≠ v) (fun _ => univ) d
  W := R
  Θ _ _ := univ
  f _ w z θ := if z w = θ then 1 else 0
  c _ _ := 0
namespace Network
end Network
end Groundwork


