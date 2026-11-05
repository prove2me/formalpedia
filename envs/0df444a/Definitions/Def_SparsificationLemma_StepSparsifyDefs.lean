-- Prove2me | Definitions.Def_SparsificationLemma_StepSparsifyDefs
-- name    : SparsificationLemma_StepSparsifyDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:54:30.747931+00:00
-- url     : https://prove2.me/theorems/7a6a7850-377e-43d7-aa45-75145894b6d7
-- title:
--   Step Sparsify Defs
-- statement:
--   Definitions and structural lemmas for Step Sparsify Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsifyDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat
def nodesOf {σ : Type} (step : σ → Option (σ × σ)) : ℕ → σ → List σ
  | 0, s => [s]
  | d + 1, s =>
    match step s with
    | none => [s]
    | some (l, h) => s :: (nodesOf step d l ++ nodesOf step d h)
namespace StepSparsify
open SparsificationLemma.Cal
def DeltaOf (n : ℕ) (Φ : PFml) : ℕ := max 2 ((range n).sup fun v => occN Φ v)
def widthOf (φ : PFml) : ℕ := φ.foldr (fun C m => max C.length m) 0
end StepSparsify
end SparsificationLemma


