-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfPad
-- name    : ClauseBound_Inst_HalfPad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:57:46.661008+00:00
-- url     : https://prove2.me/theorems/f88a8cec-162e-4757-8637-357fb9b321a5
-- title:
--   Half Pad
-- statement:
--   Definitions and structural lemmas for Half Pad, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
namespace Pad
end Pad
open Pad
end ClauseBound.Inst.Half


