-- Prove2me | Definitions.Def_CountedRecursion_CallFacts
-- name    : CountedRecursion_CallFacts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:27:34.074358+00:00
-- url     : https://prove2.me/theorems/09b42cbb-c6fd-4dd7-b21d-6a3640580e3d
-- title:
--   Call Facts
-- statement:
--   Definitions and structural lemmas for Call Facts, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallFacts.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallLemma
import Mathlib.Tactic
import Theorems.Thm_Eight_SecNetworks_L_le

set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
@[expose] noncomputable def callNet (D : PiecesCounted.Data) (c x₀ l : ℕ) (a : Ctx) (f : TableQuery → Option Ans) (y : ℕ) : Net (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) :=
  patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)
@[expose] noncomputable def callL (D : PiecesCounted.Data) (c x₀ l : ℕ) (a : Ctx) (f : TableQuery → Option Ans) (y : ℕ) : ℕ :=
  AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (callNet D c x₀ l a f y).U
@[expose] def callParent (D : PiecesCounted.Data) (x₀ l : ℕ) (a : Ctx) (y x : ℕ) : Parent :=
  mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x
structure AtCall (D : PiecesCounted.Data) (c x₀ l : ℕ) (a a' : Ctx) (f : TableQuery → Option Ans) (y x : ℕ) : Prop where
  y_lt : y < #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l)
  x_lt : x < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l
  lev : cLev a' = l
  lam : cLam a' = callL D c x₀ l a f y
  bits : cB a' = bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))
  parent : parentOf a' = callParent D x₀ l a y x
  is : (callNet D c x₀ l a f y).Is (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))
  data : netData c (callParent D x₀ l a y x) =
    ((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)), netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))
  few : ∀ (hK0 : 0 < Levels.Gen.K x₀ l) (γ : Fin (Levels.Gen.K x₀ l)),
    Levels.Gen.K x₀ l * #{v : Fin (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) | Paper.grouping hK0 x v = γ} ≤ 2 * Levels.Gen.g x₀ l
  short : ∀ (hK0 : 0 < Levels.Gen.K x₀ l) (γ γ' : Fin (Levels.Gen.K x₀ l)), γ ≠ γ' → Y (callNet D c x₀ l a f y).c (Paper.grouping hK0 x) γ γ' ≤ callL D c x₀ l a f y
  L_pos : 1 ≤ callL D c x₀ l a f y
  L_le : callL D c x₀ l a f y ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)
end ExplicitCost


