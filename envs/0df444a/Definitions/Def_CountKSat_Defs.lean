-- Prove2me | Definitions.Def_CountKSat_Defs
-- name    : CountKSat_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:44:29.304914+00:00
-- url     : https://prove2.me/theorems/5abe6298-a6db-41c9-9c4f-dcbb0d920506
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Fintype.Pi
set_option autoImplicit false
section
section
namespace CountKSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Groundwork.Stepped
abbrev CNode : Type := PFml × PFml
def negU (H : PCl) : PFml := H.map fun l => [(l.1, !l.2)]
def stepC (θ : ℕ → ℕ) (k : ℕ) (x : CNode) : Option (CNode × CNode) :=
  (pickK θ k x.1).map fun HP => ((addP [HP.1] x.1, x.2), (addP HP.2 x.1, negU HP.1 ++ x.2))
def taut (n : ℕ) : PFml := (List.range n).map fun i => [(i, true), (i, false)]
def rootC (p : List Unit × Fml) : CNode := (rootP p.2, taut p.1.length)
def leafF (x : CNode) : Fml := x.2 ++ x.1
def ext {n : ℕ} (a : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then a ⟨i, h⟩ else false
def cntN (n : ℕ) (x : Fml) : ℕ := (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ x, ∃ l ∈ C, ext a l.1 = l.2).card
variable {α ν : Type}
def walkSum [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν ℕ) : Stepped α ℕ :=
  foldWhile (fun a => some [root a]) (walkNext step) (guard (walkSel step) T 0) (fun c _ b => c + b) fun _ => 0
def outW (q : (List Unit × Fml) × ℕ) : List Bool := toWord (q.1.1.length + 1) q.2
def countMK (decU : List Bool → List Unit × Fml) (step : CNode → Option (CNode × CNode)) (M : Stepped Fml ℤ) :
    Stepped (List Bool) (List Bool) :=
  Stepped.mapIn decU (Stepped.bind
    (Stepped.ite (fun p => hasNil p.2) (Stepped.const 0) (walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat))))
    (Stepped.ofFun outW))
end CountKSat


