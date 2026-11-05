-- Prove2me | Definitions.Def_VariableBound_Net_CertNet
-- name    : VariableBound_Net_CertNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:03:33.195387+00:00
-- url     : https://prove2.me/theorems/3ef59181-8c3c-412d-aa6f-dc7d232b6f1c
-- title:
--   Cert Net
-- statement:
--   Definitions and structural lemmas for Cert Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
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
section
namespace VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]
def ok1 (g n a : ℕ) (z : List Bool) : Bool := (List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)
def ok2l (q a : ℕ) (z : List Bool) (l : ℕ × Bool) : Bool := !(l.1 / q == a) || (z.getD (l.1 % q) false != l.2)
def ok2 (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : Bool :=
  (tch g n D a).all fun o => !(mark g n D a z o) || (clOf D o).all (ok2l (qv g n) a z)
def ok3 (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range 2).all fun κ => ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length == mu g D y a a κ
def ok4 (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range g).all fun b => b == a || (List.range 2).all fun κ => (str g n D a b κ z).count true == mu g D y a b κ
def sigP (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : ℤ :=
  (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod
def sgE (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n D a).filter fun o => (obAt D o).1 == 0 && ownB g n D o a && mark g n D a z o).length
end VariableBound.Net.CertNet
namespace VariableBound.Net
end VariableBound.Net


