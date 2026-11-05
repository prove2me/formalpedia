-- Prove2me | Definitions.Def_ClauseBound_Group_Grouping
-- name    : ClauseBound_Group_Grouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:22:59.166796+00:00
-- url     : https://prove2.me/theorems/d7e2a246-7a30-48d8-9e63-4467a15b83d7
-- title:
--   Grouping
-- statement:
--   Definitions and structural lemmas for Grouping, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Group
open Finset
namespace Grouping
variable {K n : ℕ}
def chi0 (a : Fin (K * n)) : Fin K := (finProdFinEquiv.symm a).1
def cls (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : Finset (Fin (K * n)) := {a | chi0 (e a) = γ}
end Grouping
open Grouping
end ClauseBound.Group


