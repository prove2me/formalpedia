-- Prove2me | Definitions.Def_PaddedDescent_F_CertMark
-- name    : PaddedDescent_F_CertMark
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:08:12.374754+00:00
-- url     : https://prove2.me/theorems/d450dafa-25b3-4a22-a78e-77b601379360
-- title:
--   Cert Mark
-- statement:
--   Definitions and structural lemmas for Cert Mark, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
def mW1 (g n a : ℕ) (z : List Bool) : Bool := (List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)
def mW2l (q a : ℕ) (z : List Bool) (l : ℕ × Bool) : Bool := !(l.1 / q == a) || (z.getD (l.1 % q) false != l.2)
def mW2 (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : Bool :=
  (tch g n Ls a).all fun e => !(mark g n Ls a z e) || (clAt Ls e).2.all (mW2l (qv g n) a z)
def mW3 (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range Ls.length).all fun i =>
    ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length == mu g Ls y a a i
def mW4 (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i
def mWs (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length
end PaddedDescent.F.Mark.Cert
namespace PaddedDescent.F
open Groundwork Groundwork.Prog
end PaddedDescent.F


