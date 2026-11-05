-- Prove2me | Definitions.Def_UniformInK_Top_Leaves
-- name    : UniformInK_Top_Leaves
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:19:33.963468+00:00
-- url     : https://prove2.me/theorems/c10f4c74-187f-40a6-9e5a-ee0533e398f7
-- title:
--   Leaves
-- statement:
--   Definitions and structural lemmas for Leaves, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
namespace UniformInK.Leaves
open PaddedDescent
end UniformInK.Leaves
namespace UniformInK
open PaddedDescent UniformInK.Leaves
end UniformInK


