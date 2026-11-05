-- Prove2me | Definitions.Def_VariableBound_Family_Main
-- name    : VariableBound_Family_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:19:00.653346+00:00
-- url     : https://prove2.me/theorems/25b1d7c7-4fd6-4772-80a1-c67edc6af673
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Finset AppVariables VariableBound.Pairwise
namespace Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
end Family
end VariableBound


