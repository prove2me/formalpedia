-- Prove2me | Definitions.Def_Value_Joint
-- name    : Value_Joint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:15:56.312197+00:00
-- url     : https://prove2.me/theorems/35e5428b-df98-4883-b30e-767517a2e339
-- title:
--   Joint
-- statement:
--   Definitions and structural lemmas for Joint, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
set_option autoImplicit false
section
section
@[expose] section
namespace Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
def groupTerm (N : Net g) (χ : Fin g → Fin K) (θ : Fin g × Fin g → List Bool) (γ : Fin K) (z : Fin g → List Bool) : ℤ :=
  (∏ a with χ a = γ, N.W a (z a)) * (∏ p ∈ pairs (Fin g) with χ p.1 = γ ∧ χ p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
    ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, N.f p.1 p.2 (z p.1) (θ (pr p.1 p.2))
end Value


