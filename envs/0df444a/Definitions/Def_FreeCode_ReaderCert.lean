-- Prove2me | Definitions.Def_FreeCode_ReaderCert
-- name    : FreeCode_ReaderCert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:45:36.930965+00:00
-- url     : https://prove2.me/theorems/74a16815-74fd-4086-9d65-01bf20fd9a92
-- title:
--   Reader Cert
-- statement:
--   Definitions and structural lemmas for Reader Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Reader
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
end FreeCode


