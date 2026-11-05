-- Prove2me | Definitions.Def_SparsifyThenCount_PlanUsedDefs
-- name    : SparsifyThenCount_PlanUsedDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:36:04.589028+00:00
-- url     : https://prove2.me/theorems/6340055c-2ee2-41f7-9f47-c822f90b9d2e
-- title:
--   Plan Used Defs
-- statement:
--   Definitions and structural lemmas for Plan Used Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsedDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
set_option autoImplicit false
section
section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide
def PlanUsed {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ φ : Sat3.CNF n, SatK.IsKCNF k φ → (planD S pick slU (SatM.enc k φ)).isSome = true
def StPlanUsed : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) (rn rm : ℕ → ℝ) (A : List Bool × U → List Bool),
  Alg rn rm A (eBD S pick slU) → Filter.Tendsto rn Filter.atTop (nhds 0) → PlanUsed S pick slU
def StRateZero : Prop := Filter.Tendsto (SatK.rN 1 (1 / 2)) Filter.atTop (nhds 0)
end SparsifyThenCount


