-- Prove2me | Definitions.Def_GeneralPieces_Series_LemmaQ
-- name    : GeneralPieces_Series_LemmaQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:17:42.140197+00:00
-- url     : https://prove2.me/theorems/8622421a-a7f6-4ffe-b0e0-1ffe2b844ed4
-- title:
--   Lemma Q
-- statement:
--   Definitions and structural lemmas for Lemma Q, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Series
open ClauseBound.Boson Finset
@[expose] def pairF (A : FA) (b : List ℕ) : ℤ := (A.map fun c => c.1 * op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ)).sum
variable {A : FA} {b : List ℕ}
end GeneralPieces.Series


