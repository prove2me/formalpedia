-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Start
-- name    : ClauseBound_ParityChecks_Start
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:51.357038+00:00
-- url     : https://prove2.me/theorems/d5b23155-4673-49d1-8007-88393b84e58c
-- title:
--   Start
-- statement:
--   Definitions and structural lemmas for Start, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
section
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
end
end ClauseBound.ParityChecks.Start


