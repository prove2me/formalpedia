-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfTabSpec
-- name    : ClauseBound_Inst_HalfTabSpec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:38:12.402317+00:00
-- url     : https://prove2.me/theorems/6733cbe8-7409-4854-bb68-979580f7e9c8
-- title:
--   Half Tab Spec
-- statement:
--   Definitions and structural lemmas for Half Tab Spec, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
end ClauseBound.Inst.Half


