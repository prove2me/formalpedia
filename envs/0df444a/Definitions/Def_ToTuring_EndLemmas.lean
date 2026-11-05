-- Prove2me | Definitions.Def_ToTuring_EndLemmas
-- name    : ToTuring_EndLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:56.059783+00:00
-- url     : https://prove2.me/theorems/2d10f257-f1a2-48a6-b3ec-d527d5e9df27
-- title:
--   End Lemmas
-- statement:
--   Definitions and structural lemmas for End Lemmas, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
section
namespace Sat3
open Turing
open scoped NNReal ENNReal
end Sat3


