-- Prove2me | Definitions.Def_CountedRecursion_PolyLists
-- name    : CountedRecursion_PolyLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:50:06.597867+00:00
-- url     : https://prove2.me/theorems/98411909-7a51-41b5-9518-93eef60bbf86
-- title:
--   Poly Lists
-- statement:
--   Definitions and structural lemmas for Poly Lists, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]
section Lists
variable {L : α → Lists} (hL : PolyT L)
include hL
end Lists
end ExplicitCost


