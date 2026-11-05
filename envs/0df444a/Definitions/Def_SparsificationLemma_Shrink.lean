-- Prove2me | Definitions.Def_SparsificationLemma_Shrink
-- name    : SparsificationLemma_Shrink
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:52:59.843303+00:00
-- url     : https://prove2.me/theorems/9c7f1104-c854-409f-b237-e3da86e78d23
-- title:
--   Shrink
-- statement:
--   Definitions and structural lemmas for Shrink, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Shrink.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
namespace Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
end Shrink
end SparsificationLemma


