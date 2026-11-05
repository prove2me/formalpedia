-- Prove2me | Definitions.Def_RecursionToBound_Guard
-- name    : RecursionToBound_Guard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:48:03.092729+00:00
-- url     : https://prove2.me/theorems/f80cbeb1-7895-4bb6-84d7-432d625e454a
-- title:
--   Guard
-- statement:
--   Definitions and structural lemmas for Guard, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
set_option autoImplicit false
section
section
@[expose] section
namespace RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
end RecursionToBound


