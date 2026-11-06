-- Prove2me | Definitions.Def_FreeCode_Tied
-- name    : FreeCode_Tied
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:02:34.764682+00:00
-- url     : https://prove2.me/theorems/e230d160-93e2-4572-90cb-d365dcdf88f1
-- title:
--   Tied
-- statement:
--   Definitions and structural lemmas for Tied, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace FreeCode
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat
end FreeCode


