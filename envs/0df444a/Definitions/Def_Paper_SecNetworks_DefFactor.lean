-- Prove2me | Definitions.Def_Paper_SecNetworks_DefFactor
-- name    : Paper_SecNetworks_DefFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:29:31.953582+00:00
-- url     : https://prove2.me/theorems/1bf8fcb5-6d0d-4c97-997d-cb0fabf6344c
-- title:
--   Sec Networks Def Factor
-- statement:
--   Definitions and structural lemmas for Sec Networks Def Factor, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_DefFactor.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
section
section
namespace Paper
open Finset
variable {X X' : Type*}
def FactorsThrough (F : X → X' → ℤ) (c : ℕ) : Prop :=
  ∃ (f : X → (Fin c → Bool) → ℤ) (f' : X' → (Fin c → Bool) → ℤ),
    ∀ z z', F z z' = ∑ θ : Fin c → Bool, f z θ * f' z' θ
end Paper


