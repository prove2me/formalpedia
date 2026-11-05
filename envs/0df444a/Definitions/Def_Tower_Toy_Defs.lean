-- Prove2me | Definitions.Def_Tower_Toy_Defs
-- name    : Tower_Toy_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:20:25.713506+00:00
-- url     : https://prove2.me/theorems/20550e1d-fdb9-428e-b391-f5a770193f13
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace QueryMachines.Tower.Toy
open Groundwork
scoped instance encEmpty : Enc Empty := ⟨fun e => e.elim⟩
abbrev Ph : Type := Unit ⊕ (ℕ ⊕ ((ℕ × ℕ) ⊕ ℕ))
def solInit (c : ℕ × Bool) : ℕ × Ph := (c.1, Sum.inl ())
def solStep (s : ℕ × Ph) : ℕ × Ph :=
  s.2.elim (fun _ => s) fun r => r.elim (fun _ => s) fun r' => r'.elim (fun p => (s.1, Sum.inr (Sum.inr (Sum.inr (p.1 + p.2))))) fun _ => s
def solOut (s : ℕ × Ph) : Option ℕ :=
  s.2.elim (fun _ => none) fun r => r.elim (fun _ => none) fun r' => r'.elim (fun _ => none) fun v => some v
def solAsk (s : ℕ × Ph) : Option ((ℕ × Bool) ⊕ (List Bool ⊕ Empty)) :=
  s.2.elim (fun _ => if s.1 = 0 then some (Sum.inr (Sum.inl [])) else some (Sum.inl (s.1 - 1, false))) fun r => r.elim (fun _ => some (Sum.inl (s.1 - 1, true))) fun _ => none
def solResume (s : ℕ × Ph) (v : ℕ) : ℕ × Ph :=
  s.2.elim (fun _ => if s.1 = 0 then (s.1, Sum.inr (Sum.inr (Sum.inr v))) else (s.1, Sum.inr (Sum.inl v))) fun r => r.elim (fun u => (s.1, Sum.inr (Sum.inr (Sum.inl (u, v))))) fun _ => s
def Sol : QueryMachine ((ℕ × Bool) ⊕ (List Bool ⊕ Empty)) ℕ (ℕ × Bool) ℕ where
  σ := ℕ × Ph
  init := solInit
  step := solStep
  out := solOut
  ask := solAsk
  resume := solResume
def innInit (x : (ℕ × Bool) × List Bool) : (Bool × List Bool) ⊕ ℕ := Sum.inl (x.1.2, x.2)
def innOut (s : (Bool × List Bool) ⊕ ℕ) : Option ℕ := s.elim (fun _ => none) fun v => some v
def innAsk (s : (Bool × List Bool) ⊕ ℕ) : Option (List Bool ⊕ Empty) := s.elim (fun p => some (Sum.inl (p.1 :: p.2))) fun _ => none
def innResume (s : (Bool × List Bool) ⊕ ℕ) (v : ℕ) : (Bool × List Bool) ⊕ ℕ := s.elim (fun _ => Sum.inr v) fun _ => s
def Inn : QueryMachine (List Bool ⊕ Empty) ℕ ((ℕ × Bool) × List Bool) ℕ where
  σ := (Bool × List Bool) ⊕ ℕ
  init := innInit
  step := fun s => s
  out := innOut
  ask := innAsk
  resume := innResume
def sumF : ℕ → (List Bool → Option ℕ) → ℕ
  | 0, f => (f []).getD 0
  | l + 1, f => sumF l (fun q => f (false :: q)) + sumF l (fun q => f (true :: q))
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | l + 1 => (words l).map (false :: ·) ++ (words l).map (true :: ·)
def spec (ℓ0 M0 : ℕ) : Spec (ℕ × Bool) (List Bool) ℕ where
  lev c := c.1
  Good c f := c.1 ≤ ℓ0 ∧ ∀ q : List Bool, q.length = c.1 → ∃ a, a ≤ M0 ∧ f q = some a
  val c f := sumF c.1 f
  Child c _ c' := c'.1 + 1 = c.1
  tab c' f q := if q.length = c'.1 then f (c'.2 :: q) else none
def TS : ℕ → ℕ → ℕ → ℕ
  | 0, _, tq => tq
  | _ + 1, tc, _ => 2 * tc + 1
def TI (_ tq : ℕ) : ℕ := tq
def SS (ℓ0 M0 : ℕ) : ℕ := ℓ0.size + 2 * (2 ^ ℓ0 * M0).size + 6
def SI (ℓ0 M0 : ℕ) : ℕ := 2 * ℓ0 + M0.size + 5
def SC (ℓ0 : ℕ) : ℕ := ℓ0.size + 2
def noG : Empty → Option ℕ := fun e => e.elim
def noW : Empty → ℕ := fun e => e.elim
def ToyPoly : Prop := (tower Sol Inn).PolyTimeSteps
def ToyMeets : Prop := ∀ ℓ0 M0 : ℕ, (spec ℓ0 M0).Meets noG noW Sol Inn TS TI (SS ℓ0 M0) (SI ℓ0 M0) (SC ℓ0)
def ToyRuns : Prop := ∀ (ℓ M0 t : ℕ) (b : Bool) (f : List Bool → Option ℕ), (∀ q : List Bool, q.length = ℓ → ∃ a, a ≤ M0 ∧ f q = some a) →
  (tower Sol Inn).Within (Sum.elim f noG) (Sum.elim (fun _ => t) noW) (ℓ, b) (2 ^ ℓ * (t + 2 * ℓ + 5)) (towerSize ℓ (SS ℓ M0) (SI ℓ M0) (SC ℓ)) (((words ℓ).map fun q => (f q).getD 0).sum)
end QueryMachines.Tower.Toy


