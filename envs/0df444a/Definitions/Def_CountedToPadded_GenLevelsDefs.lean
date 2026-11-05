-- Prove2me | Definitions.Def_CountedToPadded_GenLevelsDefs
-- name    : CountedToPadded_GenLevelsDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:32:48.867981+00:00
-- url     : https://prove2.me/theorems/1bbb0c42-a8e1-414c-8dfb-ea80f3607380
-- title:
--   Gen Levels Defs
-- statement:
--   Definitions and structural lemmas for Gen Levels Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevelsDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CliqueLevelsStatement
import Definitions.Def_LevelsStatement
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace CliqueLevels
open Groundwork Printed
def roundUnder (b : ℕ) (s : Option (ℕ × ℕ)) : Option (ℕ × ℕ) := s.bind fun pk => if (pk.1 * pk.2) ^ 2 ≤ b then some (8 * pk.1, (pk.1 * pk.2) ^ 2) else none
def levelsUnder (x₀ : ℕ) (p : List Unit × List Unit) : Option (List Unit) :=
  (p.1.foldl (fun s _ => roundUnder p.2.length s) (if 2 ^ x₀ ≤ p.2.length then some (2 ^ x₀, 2 ^ x₀) else none)).map fun pk => unary pk.2
def LevelsAreComputed : Prop := ∀ x₀ : ℕ, ComputesLevels (Levels.Gen.K x₀) (levelsUnder x₀)
def SolvesGrowsWithTheConstant : Prop := ∀ (M : QueryMachines.QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ C₁ : ℕ), (∀ l, 1 ≤ K l) → C₀ ≤ C₁ →
  (Solves M K e C₀ → Solves M K e C₁) ∧ (SolvesInFactor M K e C₀ → SolvesInFactor M K e C₁)
end CliqueLevels


