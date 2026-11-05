-- Prove2me | Definitions.Def_MinOfBounds_Arith
-- name    : MinOfBounds_Arith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:37:30.414198+00:00
-- url     : https://prove2.me/theorems/cdbe8167-4fc2-4efb-8dea-6c47c577bd4f
-- title:
--   Arith
-- statement:
--   Definitions and structural lemmas for Arith, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace MinOfBounds
open MainTheoremForms VariableBound.Paper
end MinOfBounds


