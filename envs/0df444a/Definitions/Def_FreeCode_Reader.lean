-- Prove2me | Definitions.Def_FreeCode_Reader
-- name    : FreeCode_Reader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:38:56.170952+00:00
-- url     : https://prove2.me/theorems/260ed022-a9b3-492d-b6ff-964cc758c65f
-- title:
--   Reader
-- statement:
--   Definitions and structural lemmas for Reader, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
namespace FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
abbrev RState : Type := Bool × Bool × List Bool × List (List Bool) × List (List (List Bool))
def stepR (w : ℕ) (s : RState) (e : Bool) : RState :=
  bif s.1 then
    (bif s.2.1 then s
     else bif decide (s.2.2.1.length + 1 = w) then (false, true, [], (e :: s.2.2.1) :: s.2.2.2.1, s.2.2.2.2)
       else (true, false, e :: s.2.2.1, s.2.2.2.1, s.2.2.2.2))
  else
    (bif s.2.1 then (bif e then (true, false, [], s.2.2.2.1, s.2.2.2.2) else (false, false, [], [], s.2.2.2.1 :: s.2.2.2.2))
     else (bif e then (false, true, [], [], s.2.2.2.2) else (true, true, [], [], s.2.2.2.2)))
def scanR (x : List Bool) : RState := (x.dropWhile id).tail.foldl (stepR (width (x.takeWhile id).length)) (false, false, [], [], [])
def readFree (x : List Bool) : List Unit × Fml :=
  (List.replicate (x.takeWhile id).length (), (scanR x).2.2.2.2.reverse.map fun cl => cl.reverse.map fun cur => (slotDec (ofWord cur.reverse)).getD (0, false))
end FreeCode
section
@[expose] section
namespace FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
end FreeCode


