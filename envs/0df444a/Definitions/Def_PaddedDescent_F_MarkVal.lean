-- Prove2me | Definitions.Def_PaddedDescent_F_MarkVal
-- name    : PaddedDescent_F_MarkVal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:09:42.625195+00:00
-- url     : https://prove2.me/theorems/460a5782-ab11-41d7-af71-295d514f81ea
-- title:
--   Mark Val
-- statement:
--   Definitions and structural lemmas for Mark Val, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
def st (g n : ℕ) (Ls : List Fml) (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : List Bool :=
  (List.range (qv g n)).map (fun r => σ (a * qv g n + r)) ++ (tch g n Ls a).map fun e => decide (e ∈ P)
def base (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n Ls a).all fun e => !(mark g n Ls a z e) ||
      (clAt Ls e).2.all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2))
def ownC (g n : ℕ) (Ls : List Fml) (a i : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length
def sgE (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length
def prof (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range Ls.length).all fun i => ownC g n Ls a i z == mu g Ls y a a i) &&
    ((List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i)
abbrev ctx (g n β b : ℕ) (Ls : List Fml) (y : ℕ) : MCtx :=
  ((List.replicate g (), List.replicate n (), List.replicate β (), List.replicate b ()), (Ls, y))
def Gd (g n : ℕ) (Ls : List Fml) (z : Fin g → List Bool) : Prop :=
  (∀ a : Fin g, base g n Ls a (z a) = true) ∧
    ∀ a a' : Fin g, a < a' → ∀ i < Ls.length, str g n Ls a a' i (z a) = str g n Ls a' a i (z a')
end PaddedDescent.F.Mark.Val


