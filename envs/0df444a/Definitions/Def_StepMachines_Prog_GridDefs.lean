-- Prove2me | Definitions.Def_StepMachines_Prog_GridDefs
-- name    : StepMachines_Prog_GridDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:08.943371+00:00
-- url     : https://prove2.me/theorems/0d2622e7-c6b5-4775-b491-ad2d650df7f0
-- title:
--   Grid Defs
-- statement:
--   Definitions and structural lemmas for Grid Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
set_option autoImplicit false
section
section
namespace Groundwork.Prog
open Finset Stepped
def nRect (g : ℕ) : ℕ := g.choose 2 ^ 2
def digit (n y q : ℕ) : ℕ := y / (n + 1) ^ q % (n + 1)
def tb (c : ℕ) : ℕ := Nat.size (3 ^ c)
def capW (n c : ℕ) : ℕ := n + tb c
def priceRow (g n y : ℕ) : ℕ := 2 * ∑ q ∈ range (nRect g), capW n (n - digit n y q)
def priceCol (g n y : ℕ) : ℕ := 2 * ∑ q ∈ range (nRect g), capW n (digit n y q)
abbrev NetFormer : Type 1 :=
  {C : Type} → [HasSize C] → (C → ℕ) → Stepped (C × IQ) ℤ → PNet (C × ℕ)
abbrev SideNet (g : ℕ) : Type :=
  ℕ → Inst (Fin (g * g)) (List Bool) → ℕ → Network (Fin g) (List Bool) (List Bool)
def BoundedInst {K : ℕ} (n B : ℕ) (Rm : Inst (Fin K) (List Bool)) : Prop :=
  ∀ v θ, (∀ u, u ≠ v → (θ u).length = n) → θ v = [] → |Rm v θ| ≤ 2 ^ B
end Groundwork.Prog


