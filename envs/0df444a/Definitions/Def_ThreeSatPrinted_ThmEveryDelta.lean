-- Prove2me | Definitions.Def_ThreeSatPrinted_ThmEveryDelta
-- name    : ThreeSatPrinted_ThmEveryDelta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:27:39.464297+00:00
-- url     : https://prove2.me/theorems/08229928-c882-4dfa-98ae-fd6e199cd329
-- title:
--   Thm Every Delta
-- statement:
--   Definitions and structural lemmas for Thm Every Delta, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatPrinted_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace ThreeSatPrinted
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight ThreeSatOnTree
end ThreeSatPrinted


