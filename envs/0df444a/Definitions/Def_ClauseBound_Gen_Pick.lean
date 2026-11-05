-- Prove2me | Definitions.Def_ClauseBound_Gen_Pick
-- name    : ClauseBound_Gen_Pick
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:26:34.188775+00:00
-- url     : https://prove2.me/theorems/cfe24545-235f-4c6a-89db-9954b719a6d6
-- title:
--   Pick
-- statement:
--   Definitions and structural lemmas for Pick, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
abbrev St : Type := U × List Step × U × U × U
def state (P : PiecesF) (x₀ l : ℕ) : St :=
  (rep l, sched P x₀ l, rep (K x₀ l), rep (2 ^ (3 * l + x₀)), rep (3 * P.m * 2 ^ (l + 4)))
def next (b : U) (st : St) : St :=
  if (st.2.2.2.1.length * st.2.2.1.length) ^ 2 ≤ b.length then
    (() :: st.1,
      ((st.2.2.1, List.replicate (st.2.2.2.1.length * st.2.2.1.length) (), List.replicate (st.2.2.2.1.length * st.2.2.1.length) ()),
        (st.2.2.2.2, []), (false, [], [])) :: st.2.1,
      List.replicate ((st.2.2.2.1.length * st.2.2.1.length) ^ 2) (), List.replicate (8 * st.2.2.2.1.length) (), st.2.2.2.2 ++ st.2.2.2.2)
  else st
def stepB (m k : ℕ) : ℕ := 12 * k + 192 * (m * k) + 31
def lenB (m r k : ℕ) : ℕ := r * stepB m k + 4 * r + 36 * k + 1536 * (m * k) + 18
def padOf (m x₀ : ℕ) (b : U) : U := List.replicate (lenB m b.length (b.length + 2 ^ x₀)) ()
def loop (P : PiecesF) (x₀ : ℕ) (b : U) : St :=
  (List.replicate b.length ()).foldl (fun st _ => cap (padOf P.m x₀ b) ([], [], [], [], []) (next b st))
    (cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ 0))
def pick (P : PiecesF) (x₀ : ℕ) (b : U) : U × (List Step × U) := ((loop P x₀ b).1, ((loop P x₀ b).2.1, rep (K x₀ 0)))
end ClauseBound.Gen.Pick


