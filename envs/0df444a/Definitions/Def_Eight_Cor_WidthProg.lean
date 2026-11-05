-- Prove2me | Definitions.Def_Eight_Cor_WidthProg
-- name    : Eight_Cor_WidthProg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:45:54.481833+00:00
-- url     : https://prove2.me/theorems/a3778727-3661-418b-bcb6-4639fb5faf17
-- title:
--   Width Prog
-- statement:
--   Definitions and structural lemmas for Width Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Eight.Width
open Groundwork Groundwork.Prog CountKSat
def freshN (n N : ℕ) : List ℕ := (List.range N).map fun i => n + i
def splitN (n : ℕ) (x : Fml) : Fml := (splitAll (freshN n (numFresh x)) x).dedup
def widthP (p : List Unit × Fml) : List Unit × Fml :=
  (List.replicate (p.1.length + numFresh p.2) (), splitN p.1.length p.2)
def clauseP (ys : List ℕ) (C : List (ℕ × Bool)) : Fml :=
  (ys.zip ((C.headD (0, false) :: ys.map fun y => (y, true)).zip C.tail)).flatMap (fun q => forced q.1 q.2.1 q.2.2) ++
    [if ys.isEmpty then C else (ys.getLast?.getD 0, true) :: C.drop (ys.length + 1)]
def allP (ys : List ℕ) (x : Fml) : Fml :=
  (List.range x.length).flatMap fun j =>
    clauseP ((ys.drop (numFresh (x.take j))).take ((x.getD j []).length - 3)) (x.getD j [])
end Eight.Width


