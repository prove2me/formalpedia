-- Prove2me | Definitions.Def_Eight_Cor_Width
-- name    : Eight_Cor_Width
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:38.793909+00:00
-- url     : https://prove2.me/theorems/4c46be31-55cd-466b-8710-823527d1a833
-- title:
--   Width
-- statement:
--   Definitions and structural lemmas for Width, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
section fin
variable {n : ℕ}
@[expose] def freshFin (n N : ℕ) : List (Fin (n + N)) := (List.finRange N).map (Fin.natAdd n)
@[expose] def lift (N : ℕ) (φ : CNF n) : CNF (n + N) := φ.map fun C => C.map fun l => (Fin.castAdd N l.1, l.2)
end fin
end Eight.Width


