-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Num
-- name    : ClauseBound_ParityChecks_Num
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:27.022043+00:00
-- url     : https://prove2.me/theorems/e49f2448-ae95-42be-ab9c-5243cf5c8000
-- title:
--   Num
-- statement:
--   Definitions and structural lemmas for Num, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
@[expose] def ChkOK (e : ℕ) (L : Chk) : Prop := L.Nodup ∧ ∀ x ∈ L, x < e
namespace Num
end Num
namespace Num
variable {q}
end Num
end ClauseBound.ParityChecks


