-- Prove2me | Definitions.Def_Tower_Chain
-- name    : Tower_Chain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:20:16.551408+00:00
-- url     : https://prove2.me/theorems/e454e847-a4da-4d29-9f88-c624fff031ae
-- title:
--   Chain
-- statement:
--   Definitions and structural lemmas for Chain, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)
def tabs : List Ctx → Q → Option A
  | [] => f0
  | c :: env => P.tab c (tabs env)
def parent : List Ctx → Ctx
  | [] => c0
  | c :: _ => c
def Chain : List Ctx → Prop
  | [] => True
  | c :: env => Chain env ∧ P.Child (parent c0 env) (tabs P f0 env) c
def price : List Ctx → ℕ
  | [] => tq
  | c :: env => TI (P.lev c) (price env) + 2
def callCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | l + 1, t => cost TS TI l (TI l t + 2) + 2
def nGood : NIn Ctx Q → Prop
  | Sum.inl (env, c) => Chain P c0 f0 env ∧ c = parent c0 env
  | Sum.inr (c, env, q) => Chain P c0 f0 (c :: env) ∧ (P.tab c (tabs P f0 env) q).isSome
def nval : NIn Ctx Q → A
  | Sum.inl (env, c) => P.val c (tabs P f0 env)
  | Sum.inr (c, env, q) => (P.tab c (tabs P f0 env) q).getD (P.val c0 f0)
def ndep : NIn Ctx Q → ℕ
  | Sum.inl (env, c) => 2 * P.lev c + env.length + 1
  | Sum.inr (_, env, _) => env.length
def nT : NIn Ctx Q → ℕ
  | Sum.inl (env, c) => cost TS TI (P.lev c) (price P TI tq env)
  | Sum.inr (c, env, _) => TI (P.lev c) (price P TI tq env)
variable {P TS TI c0 f0} [HasSize Ctx] {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A} {SS SI SC : ℕ}
end QueryMachines.Tower


