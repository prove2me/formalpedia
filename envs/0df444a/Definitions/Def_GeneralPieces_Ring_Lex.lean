-- Prove2me | Definitions.Def_GeneralPieces_Ring_Lex
-- name    : GeneralPieces_Ring_Lex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:35.319718+00:00
-- url     : https://prove2.me/theorems/012f6588-f75f-4647-bc02-0e41b59b67bb
-- title:
--   Lex
-- statement:
--   Definitions and structural lemmas for Lex, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Lex
open AppHalfPieces Finset
section Rank
variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)
end Rank
end GeneralPieces.Lex
namespace GeneralPieces
end GeneralPieces


