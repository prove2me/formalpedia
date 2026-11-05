-- Prove2me | Definitions.Def_StepMachines_Prog_CountNet
-- name    : StepMachines_Prog_CountNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:42.862284+00:00
-- url     : https://prove2.me/theorems/3494ca42-ef27-4094-87d5-9544b30c1102
-- title:
--   Count Net
-- statement:
--   Definitions and structural lemmas for Count Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
namespace Groundwork.Prog
open Finset SatNet
public abbrev Fml : Type := List (List (ℕ × Bool))
namespace Count
@[expose] public def mu (g : ℕ) (φ : Fml) : ℕ := (φ.length + g - 1) / g
@[expose] public def litAt (k : ℕ) (φ : Fml) (i : ℕ) : Option (ℕ × Bool) :=
  ((φ.getD (i / k) []).map some).getD (i % k) none
@[expose] public def varAt (k : ℕ) (φ : Fml) (i : ℕ) : Option ℕ := (litAt k φ i).map Prod.fst
@[expose] public def slotsOf (k : ℕ) (φ : Fml) : List ℕ := List.range (φ.flatMap fun _ => List.replicate k ()).length
@[expose] public def linkB (k : ℕ) (φ : Fml) (i i' : ℕ) : Bool :=
  decide (i < i') && (varAt k φ i).isSome && (varAt k φ i == varAt k φ i') &&
    (slotsOf k φ).all fun t => !(decide (i < t) && decide (t < i') && (varAt k φ t == varAt k φ i))
@[expose] public def locals (g k : ℕ) (φ : Fml) : List ℕ := (slotsOf k φ).take (mu g φ * k)
@[expose] public def rows (g : ℕ) (φ : Fml) : List ℕ := (List.range φ.length).take (mu g φ)
@[expose] public def links (g k : ℕ) (φ : Fml) (a b : ℕ) : List (ℕ × ℕ) :=
  (locals g k φ ×ˢ locals g k φ).filter fun p => linkB k φ (a * (mu g φ * k) + p.1) (b * (mu g φ * k) + p.2)
@[expose] public def capF (g k : ℕ) (φ : Fml) (a b : ℕ) : ℕ := (links g k φ (min a b) (max a b)).length
@[expose] public def wF (g k : ℕ) (x : Fml × WQ) : ℤ :=
  if ((locals g k x.1).all fun r => (litAt k x.1 (x.2.1 * (mu g x.1 * k) + r)).isSome || !(x.2.2.getD r false)) &&
      ((rows g x.1).all fun c => !(decide (x.2.1 * mu g x.1 + c < x.1.length)) ||
        (List.range k).any fun j =>
          (litAt k x.1 ((x.2.1 * mu g x.1 + c) * k + j)).map Prod.snd == some (x.2.2.getD (c * k + j) false)) &&
      ((links g k x.1 x.2.1 x.2.1).all fun p => x.2.2.getD p.1 false == x.2.2.getD p.2 false)
  then 1 else 0
@[expose] public def fF (g k : ℕ) (x : Fml × FQ) : ℤ :=
  if x.2.1.1 < x.2.1.2 then
    (if ((links g k x.1 x.2.1.1 x.2.1.2).zip x.2.2.2).all fun p => x.2.2.1.getD p.1.1 false == p.2 then 1 else 0)
  else (if ((links g k x.1 x.2.1.2 x.2.1.1).zip x.2.2.2).all fun p => x.2.2.1.getD p.1.2 false == p.2 then 1 else 0)
@[expose] public def wordNet (g k : ℕ) (φ : Fml) : Network (Fin g) (List Bool) (List Bool) where
  S _ := words (mu g φ * k)
  W a z := wF g k (φ, (a.val, z))
  Θ a b := words (capF g k φ a.val b.val)
  f a b z θ := fF g k (φ, ((a.val, b.val), (z, θ)))
  c a b := capF g k φ a.val b.val
variable {g μ k : ℕ} {φ : Fml}
@[expose] public def loc (s : Sl μ k) : ℕ := s.1.val * k + s.2.val
@[expose] public def bits (z : List Bool) : Sl μ k → Bool := fun s => z.getD (loc s) false
end Count
end Groundwork.Prog


