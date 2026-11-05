-- Prove2me | Definitions.Def_OccurM_Main
-- name    : OccurM_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:42:44.535548+00:00
-- url     : https://prove2.me/theorems/a65894be-963e-4b76-976e-2e689d502e58
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
set_option autoImplicit false
section
section
@[expose] section
namespace ClausesOccur
open Turing MainTheoremForms
end ClausesOccur
namespace OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
end OccurM
namespace ClausesOccur
open Turing MainTheoremForms
end ClausesOccur


