-- Prove2me | Definitions.Def_StepMachines_Prog_Brute
-- name    : StepMachines_Prog_Brute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:21:17.049422+00:00
-- url     : https://prove2.me/theorems/da579d6e-a750-461c-a1c6-89e8d663c0d9
-- title:
--   Brute
-- statement:
--   Definitions and structural lemmas for Brute, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
set_option autoImplicit false
section
namespace Groundwork
open Finset Stepped
@[expose] public def Inst.ZW {J : Type*} [Fintype J] [LinearOrder J] (ℓ : ℕ) (d : List Bool) (R : Inst J (List Bool)) : ℤ :=
  ∑ Λ ∈ tuples (fun p : J × J => p.1 < p.2) (fun _ => words ℓ) d, ∏ v, R v (star Λ v)
@[expose] public def labelling (K ℓ : ℕ) (d w : List Bool) : Fin K × Fin K → List Bool :=
  fun p => if p.1 < p.2 then block ℓ (tri p.1 p.2) w else d
@[expose] public def query0 (K ℓ : ℕ) (d w : List Bool) (v : ℕ) : ℕ × List (List Bool) :=
  (v, (List.range K).map fun u => if u = v then d else block ℓ (tri (min v u) (max v u)) w)
variable {C : Type} [HasSize C]
@[expose] public def bruteBound (K : ℕ) (lam : C → ℕ) (c : C) : ℕ := 2 ^ (K * (K - 1) / 2 * lam c)
@[expose] public def bruteQuery (K : ℕ) (lam : C → ℕ) (dflt : C → List Bool) (x : (C × ℕ) × ℕ) :
    C × ℕ × List (List Bool) :=
  (x.1.1, query0 K (lam x.1.1) (dflt x.1.1) (toWord (K * (K - 1) / 2 * lam x.1.1) x.1.2) x.2)
@[expose] public def brute (K : ℕ) (lam : C → ℕ) (dflt : C → List Bool) (R : Stepped (C × ℕ × List (List Bool)) ℤ) :
    Stepped C ℤ :=
  sumRange (bruteBound K lam) (prodRange (Function.const (C × ℕ) K) (mapIn (bruteQuery K lam dflt) R))
end Groundwork


