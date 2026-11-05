-- Prove2me | Definitions.Def_ClauseBound_Gen_Rate
-- name    : ClauseBound_Gen_Rate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:24:54.636596+00:00
-- url     : https://prove2.me/theorems/580c037d-92a8-4889-ac98-4fe407915e2c
-- title:
--   Rate
-- statement:
--   Definitions and structural lemmas for Rate, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
noncomputable def Bd (ρ : ℝ) (c x₀ l lam B : ℕ) : ℝ :=
  e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + (6 * c + 14) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))
end ClauseBound.Gen.Rate


