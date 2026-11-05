-- Prove2me | Definitions.Def_ClauseBound_Alg_NeedC
-- name    : ClauseBound_Alg_NeedC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:32:04.221827+00:00
-- url     : https://prove2.me/theorems/d26a4efe-6581-4f2f-a243-c255dc5443f7
-- title:
--   Need C
-- statement:
--   Definitions and structural lemmas for Need C, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
@[expose] def tot (P : PiecesF) (st : NState) (sched : List Step) : ℕ :=
  max st.2.2.2 (needG P st.2.2.1 st.1.1.length st.1.2 st.2.1.1 st.2.1.2 sched)
end ClauseBound.Alg.NeedC


