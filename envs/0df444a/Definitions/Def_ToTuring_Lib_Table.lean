-- Prove2me | Definitions.Def_ToTuring_Lib_Table
-- name    : ToTuring_Lib_Table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:24:31.061595+00:00
-- url     : https://prove2.me/theorems/c11c7971-1ebb-4d8e-9de6-27fa97a7a677
-- title:
--   Table
-- statement:
--   Definitions and structural lemmas for Table, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false
section
section
namespace Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]
def lookup [DecidableEq β] (F : β → γ) (d : γ) (l : List β) (y : β) : γ :=
  l.foldr (fun b r => if y = b then F b else r) d
end Groundwork.PolyT


