-- Prove2me | Definitions.Def_ClauseBound_TopN_EvalW
-- name    : ClauseBound_TopN_EvalW
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:57:53.543568+00:00
-- url     : https://prove2.me/theorems/298a377f-078f-407c-bd6e-2d924f650d77
-- title:
--   Eval W
-- statement:
--   Definitions and structural lemmas for Eval W, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
def tl (g : ℕ) (Ls : List Fml) (y i : ℕ) : ℕ := ((List.range g).map fun a => mu g Ls y a a i).sum
def GW (R : ℕ) (ws : List ℤ) (lo hi : List ℕ) (t : ℕ → ℕ) : ℤ :=
  ∏ i ∈ range R, if lo.getD i 0 ≤ t i ∧ t i ≤ hi.getD i 0 then (ws.getD i 0 * (if i = 0 then 1 else -1)) ^ t i else 0
def truncW (n : ℕ) (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) : ℤ :=
  ∑ σ : Fin n → Bool, ((List.range Ls.length).map fun i =>
    ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio (Mark.ext σ) (Ls.getD i [])).choose j : ℤ)).prod
end ClauseBound.TopN.EvalW


