-- Prove2me | Definitions.Def_Eight_SecCrossing_Fact
-- name    : Eight_SecCrossing_Fact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:45.166323+00:00
-- url     : https://prove2.me/theorems/7ba8760a-2a1c-4d56-8265-472164ddc51a
-- title:
--   Sec Crossing Fact
-- statement:
--   Definitions and structural lemmas for Sec Crossing Fact, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
@[expose] def StSubsets : Prop := ∀ (lam i : ℕ) (x y u v : Pieces.Bits lam), A lam i x y u v =
  ∑ Q ∈ (range (tOf lam)).powersetCard i, ∏ s ∈ range (tOf lam),
    if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)
namespace Fact
end Fact
end Eight


