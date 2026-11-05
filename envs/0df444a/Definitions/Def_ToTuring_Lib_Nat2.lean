-- Prove2me | Definitions.Def_ToTuring_Lib_Nat2
-- name    : ToTuring_Lib_Nat2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T18:36:58.823708+00:00
-- url     : https://prove2.me/theorems/cf56bdea-6616-4435-97b9-5cc6b022dd49
-- title:
--   Nat2
-- statement:
--   Definitions and structural lemmas for Nat2, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
namespace Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
def divStep (d : ℕ) (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if d ≤ s.2 + s.2 + b.toNat then (s.1 + s.1 + 1, s.2 + s.2 + b.toNat - d) else (s.1 + s.1, s.2 + s.2 + b.toNat)
end Groundwork.PolyT


