-- Prove2me | Definitions.Def_ClauseBound_Gen_Defs
-- name    : ClauseBound_Gen_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:17:00.310382+00:00
-- url     : https://prove2.me/theorems/7c0d9715-ed85-4d50-8d00-6e9408f30b2c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_LevelsStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
def rep (n : ℕ) : U := List.replicate n ()
structure Par (P : PiecesF) (ρ : ℝ) (c : ℕ) : Prop where
  spec : ∀ h lam, 1 ≤ lam → P.Spec h lam
  caps : ∀ h lam, 1 ≤ lam → (capSum P h lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  cnt : ∀ h lam, 1 ≤ lam → P.cnt h lam ≤ (2 * lam) ^ c
  bits : ∀ h lam, 1 ≤ lam → P.bits h lam ≤ (2 * lam) ^ c
  d : ∀ h lam, 1 ≤ lam → P.d h lam < 2 ^ (2 * lam) ^ c
  need : ∀ h lam, 1 ≤ lam → P.need h lam ≤ c * lam
  m_le : P.m ≤ c
def step (P : PiecesF) (x₀ l : ℕ) : Step :=
  ((rep (K x₀ l), rep (g x₀ l), rep (g x₀ l)), (rep (3 * P.m * 2 ^ (l + 4)), []), (false, [], []))
def sched (P : PiecesF) (x₀ : ℕ) : ℕ → List Step
  | 0 => []
  | l + 1 => step P x₀ l :: sched P x₀ l
def idx (P : PiecesF) (x₀ l : ℕ) : List Step × U := (sched P x₀ l, rep (K x₀ 0))
def StPick : Prop := ∀ (P : PiecesF) (x₀ : ℕ), ∃ pick : U → U × (List Step × U), PolyT pick ∧
  (∀ b, (pick b).2 = idx P x₀ (pick b).1.length) ∧ (∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length) ∧
  ∀ b, b.length < K x₀ ((pick b).1.length + 1)
end ClauseBound.Gen


