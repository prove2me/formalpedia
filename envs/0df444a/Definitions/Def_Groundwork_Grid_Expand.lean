-- Prove2me | Definitions.Def_Groundwork_Grid_Expand
-- name    : Groundwork_Grid_Expand
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:26.0558+00:00
-- url     : https://prove2.me/theorems/793ef962-05d7-4560-99c1-b98a2af343d1
-- title:
--   Expand
-- statement:
--   Definitions and structural lemmas for Expand, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Expand.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Cross_Bit
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
def trHalf (ρ γ α : Type) : Half ρ γ α ≃ Half γ ρ α where
  toFun ℓ w w' := ℓ w.swap w'.swap
  invFun ℓ w w' := ℓ w.swap w'.swap
  left_inv _ := rfl
  right_inv _ := rfl
end Groundwork.Grid


