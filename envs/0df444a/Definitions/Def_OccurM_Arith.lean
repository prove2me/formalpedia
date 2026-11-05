-- Prove2me | Definitions.Def_OccurM_Arith
-- name    : OccurM_Arith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:47:06.217817+00:00
-- url     : https://prove2.me/theorems/8f5dbfac-0815-4720-915a-bfe54e0deb30
-- title:
--   Arith
-- statement:
--   Definitions and structural lemmas for Arith, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
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
namespace ClausesOccur
open MainTheoremForms
end ClausesOccur
namespace OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
def stepsC (q G : ℕ) : ℕ := max (4 * q + 2 * q * G) (q * 4 ^ q)
end OccurM


