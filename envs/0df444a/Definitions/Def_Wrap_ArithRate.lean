-- Prove2me | Definitions.Def_Wrap_ArithRate
-- name    : Wrap_ArithRate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:29:56.365006+00:00
-- url     : https://prove2.me/theorems/a79ffaca-95e1-4797-a1d9-de63e6a5f864
-- title:
--   Arith Rate
-- statement:
--   Definitions and structural lemmas for Arith Rate, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace Wrap
open MainTheoremForms
namespace Arith
end Arith
open Arith
end Wrap


