-- Prove2me | Definitions.Def_VariableBound_Net_Val
-- name    : VariableBound_Net_Val
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:04:31.896579+00:00
-- url     : https://prove2.me/theorems/61b20c11-e42c-438f-9b55-76fcc81e3c1d
-- title:
--   Val
-- statement:
--   Definitions and structural lemmas for Val, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
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
namespace VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
def st (g n : ℕ) (D : Dat) (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : List Bool :=
  (List.range (qv g n)).map (fun r => σ (a * qv g n + r)) ++ (tch g n D a).map fun e => decide (e ∈ P)
def base (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n D a).all fun e => !(mark g n D a z e) ||
      (clOf D e).all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2))
def ownC (g n : ℕ) (D : Dat) (a i : ℕ) (z : List Bool) : ℕ :=
  ((tch g n D a).filter fun e => (obAt D e).1 == i && ownB g n D e a && mark g n D a z e).length
def prof (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range 2).all fun i => ownC g n D a i z == mu g D y a a i) &&
    ((List.range g).all fun a' => a' == a || (List.range 2).all fun i => (str g n D a a' i z).count true == mu g D y a a' i)
def wz (g n : ℕ) (D : Dat) (fl : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod *
    (bif fl then (-1) ^ ownC g n D a 0 z else 1)
def Gd (g n : ℕ) (D : Dat) (z : Fin g → List Bool) : Prop :=
  (∀ a : Fin g, base g n D a (z a) = true) ∧
    ∀ a a' : Fin g, a < a' → ∀ i < 2, str g n D a a' i (z a) = str g n D a' a i (z a')
end VariableBound.Net.Val


