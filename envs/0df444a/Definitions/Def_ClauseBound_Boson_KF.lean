-- Prove2me | Definitions.Def_ClauseBound_Boson_KF
-- name    : ClauseBound_Boson_KF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:18:24.005226+00:00
-- url     : https://prove2.me/theorems/f9cad814-7383-4036-8786-0f5290166fa7
-- title:
--   KF
-- statement:
--   Definitions and structural lemmas for KF, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Boson
open Finset
@[expose] def KF (μ : List ℕ) (w : ℕ) (r : ℤ) : Ker := fun π σ =>
  ((aFam μ).map fun c => if c.2.sum = w then c.1 * op c.2 r π σ else 0).sum
end ClauseBound.Boson


