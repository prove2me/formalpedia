-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Shape
-- name    : ClauseBound_ParityChecks_Shape
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:03:40.546676+00:00
-- url     : https://prove2.me/theorems/15083da3-1f8b-4a7e-8ac3-3eca05ac7d7c
-- title:
--   Shape
-- statement:
--   Definitions and structural lemmas for Shape, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Theorems.Thm_Groundwork_PolyT_any
attribute [local fun_prop] Groundwork.PolyT.any


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
@[expose] def hasV (v : ℕ) (C : List (ℕ × Bool)) : Bool := C.any fun l => l.1 == v
section Layers
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}
end Layers
end ClauseBound.ParityChecks.Shape


