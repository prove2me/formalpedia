-- Prove2me | Definitions.Def_StepMachines_Prog_NetVal
-- name    : StepMachines_Prog_NetVal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:57:28.012347+00:00
-- url     : https://prove2.me/theorems/fad4dbdc-9d98-486c-b405-24400855c558
-- title:
--   Net Val
-- statement:
--   Definitions and structural lemmas for Net Val, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
set_option autoImplicit false
section
namespace Groundwork
open Finset
namespace Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
@[expose] public def chi (hK : 0 < K) (x : ℕ) (a : Fin g) : Fin K := ⟨col K x a, Nat.mod_lt _ hK⟩
def membersF (K : ℕ) {g : ℕ} (x G : ℕ) : List (Fin g) := (List.finRange g).filter fun a => col K x a == G
def prsF (K : ℕ) {g : ℕ} (x G G' : ℕ) : List (Fin g × Fin g) :=
  (membersF K x G).flatMap fun a => (membersF K x G').map fun b => (a, b)
@[expose] public def mD (K g : ℕ) (Np : PNet C) (c : C) (x β : ℕ) (G G' : Fin K) : Finset (List Bool) :=
  (words β).filter fun θ => (θ.drop (lbLen K g Np c x G G')).all fun b => !b
@[expose] public def mdec (K g : ℕ) (Np : PNet C) (c : C) (x : ℕ) (G G' : Fin K) (θ : List Bool) :
    Fin g × Fin g → List Bool :=
  fun p => lAt K g Np c x G G' θ (p.1.val, p.2.val)
section
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
end
end Prog.NetE
end Groundwork


