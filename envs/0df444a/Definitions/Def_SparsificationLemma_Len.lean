-- Prove2me | Definitions.Def_SparsificationLemma_Len
-- name    : SparsificationLemma_Len
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:52:18.704474+00:00
-- url     : https://prove2.me/theorems/64d6bb0f-2db3-4347-8aa4-58f063d2ebde
-- title:
--   Len
-- statement:
--   Definitions and structural lemmas for Len, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Len.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
end SparsificationLemma


