-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Congr
-- name    : ClauseBound_ParityChecks_Congr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:27.87963+00:00
-- url     : https://prove2.me/theorems/9972ce73-9089-4c66-a19b-04f1a0877f2e
-- title:
--   Congr
-- statement:
--   Definitions and structural lemmas for Congr, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Congr.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks
open Finset _root_.ParityChecks
namespace Congr
end Congr
open Congr
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)
end ClauseBound.ParityChecks


