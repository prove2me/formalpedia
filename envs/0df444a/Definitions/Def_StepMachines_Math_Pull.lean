-- Prove2me | Definitions.Def_StepMachines_Math_Pull
-- name    : StepMachines_Math_Pull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:32.646988+00:00
-- url     : https://prove2.me/theorems/98b508af-517a-46d9-8cf1-fa1cc48639b4
-- title:
--   Pull
-- statement:
--   Definitions and structural lemmas for Pull, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
set_option autoImplicit false
section
namespace Groundwork
open Finset
namespace Network
variable {J σ τ : Type*}
@[expose] public def pull [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
    (cl : ∀ a b, Code (N.Θ a b) (N.c a b)) : Network J (List Bool) (List Bool) where
  S a := words (n a)
  W a z := N.W a ((cs a).dec z)
  Θ a b := words (N.c a b)
  f a b z θ := if θ ∈ (cl (min a b) (max a b)).D then N.f a b ((cs a).dec z) ((cl (min a b) (max a b)).dec θ) else 0
  c := N.c
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
end Network
end Groundwork


