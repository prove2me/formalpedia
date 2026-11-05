-- Prove2me | Definitions.Def_Printed_CodingDefs
-- name    : Printed_CodingDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:36:32.678705+00:00
-- url     : https://prove2.me/theorems/983c4175-4754-41b6-afa5-b10503cbbc77
-- title:
--   Coding Defs
-- statement:
--   Definitions and structural lemmas for Coding Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/CodingDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
def listTables (K : ℕ) (W : ℕ → List Bool → ℤ) : Paper.Tables K := fun v θ => W v.val (List.ofFn θ).flatten
def StAskServes : Prop := ∀ (C : Type) [HasSize C] (K lam B : ℕ) (W : ℕ → List Bool → ℤ) (c : C), (∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) →
  ServesInst ((askTable : QueryMachine TableQuery ℤ (C × IQ) ℤ).close (tables K lam W)) c lam B 1 (size c + size K + K * (2 * lam + 2) + B + 3) (listTables K W)
def StCliqueValue : Prop := ∀ (K lam : ℕ) (W : ℕ → List Bool → ℤ), 2 ≤ K → 1 ≤ lam → (clique K lam fun w => W w.val).value = Paper.cliqueValue lam (listTables K W)
def StToLists : Prop := ∀ (K lam : ℕ) (w : Fin K), ∀ z ∈ words ((K - 1) * lam),
  toLists K lam (w.val, z) = (w.val, List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z) ∧
  (∀ u : Fin K, u ≠ w → (copyAt lam w u z).length = lam) ∧ toTable (toLists K lam (w.val, z)) = (w.val, z)
end Printed


