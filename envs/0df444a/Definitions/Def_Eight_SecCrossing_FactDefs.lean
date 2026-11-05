-- Prove2me | Definitions.Def_Eight_SecCrossing_FactDefs
-- name    : Eight_SecCrossing_FactDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:29:37.037884+00:00
-- url     : https://prove2.me/theorems/29cbf9b9-7f7d-4ff0-8630-a42198dce10b
-- title:
--   Sec Crossing Fact Defs
-- statement:
--   Definitions and structural lemmas for Sec Crossing Fact Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_FactDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
namespace Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
def lenW (tr : Bool) (Q : List Bool) (t : ℕ) : ℕ := 3 * t + 3 * (List.range t).countP (wide tr Q)
def StChunk : Prop := ∀ (tr : Bool) (t : ℕ) (Q a b a' b' : List Bool),
  ∑ w ∈ words (lenW tr Q t), prodL t (topAt tr Q w a b) * prodL t (botAt tr Q w a' b') =
    ∏ s ∈ range t, if wide tr Q s = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s)
end Eight


