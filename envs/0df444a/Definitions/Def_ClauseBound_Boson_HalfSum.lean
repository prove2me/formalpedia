-- Prove2me | Definitions.Def_ClauseBound_Boson_HalfSum
-- name    : ClauseBound_Boson_HalfSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:18:07.656194+00:00
-- url     : https://prove2.me/theorems/cbb24e92-f8c7-4d10-876c-08890275025b
-- title:
--   Half Sum
-- statement:
--   Definitions and structural lemmas for Half Sum, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Boson.HalfSum
open Finset
variable {lam h : ℕ} (enc : Pieces.Bits lam → Nat.Partition h)
end ClauseBound.Boson.HalfSum


