-- Prove2me | Definitions.Def_SingleBitPieces_SecProof_Cost
-- name    : SingleBitPieces_SecProof_Cost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:22:27.242199+00:00
-- url     : https://prove2.me/theorems/55ce823e-8791-4eb8-892f-aedc9cdbbbb4
-- title:
--   Sec Proof Cost
-- statement:
--   Definitions and structural lemmas for Sec Proof Cost, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecProof_Cost.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper
end SingleBitPieces


