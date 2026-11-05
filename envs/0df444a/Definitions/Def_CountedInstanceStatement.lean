-- Prove2me | Definitions.Def_CountedInstanceStatement
-- name    : CountedInstanceStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:57:36.211871+00:00
-- url     : https://prove2.me/theorems/e384e7e9-9cb0-4c9a-be62-1c61c77afb97
-- title:
--   Counted Instance Statement
-- statement:
--   Definitions and structural lemmas for Counted Instance Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/CountedInstanceStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_PairsToBound_Defs
set_option autoImplicit false
section
section
namespace CountedInstance
open Groundwork QueryMachines Printed ExplicitCost
def ThePairsMeetTheClauses : Prop :=
  ∀ x₀ C₀ : ℕ, 18 ≤ x₀ → 10 ≤ C₀ →
    CliqueLevels.Levels (Levels.Gen.K x₀) (Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ ∧
    CliqueLevels.ComputesLevels (Levels.Gen.K x₀) (CliqueLevels.levelsUnder x₀) ∧
    CliqueLevels.NumberBetween (Levels.Gen.K x₀) (Levels.Gen.e (1 / Real.sqrt 2) x₀) PairsToBound.fractionHalf ∧
    ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (MainTheoremForms.lg (Levels.Gen.K x₀ l))
def AreThePiecesOfAppHalfPieces (D : PiecesCounted.Data) : Prop :=
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    (D.fam lam).I = Finset.Icc (-(2 * (AppHalfPieces.hOf lam : ℤ))) (2 * (AppHalfPieces.hOf lam : ℤ)) ∧ (D.fam lam).d = (AppHalfPieces.hOf lam).factorial ∧
    ∀ s ∈ (D.fam lam).I, ∀ x y u v, ((D.fam lam).A s x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu s x y u v
def TheRecursionMeetsTheHypothesis : Prop :=
  ∃ (c x₀ C₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans),
    PiecesCounted.IsPieces (1 / Real.sqrt 2) (c + 2) D Alg ∧ (∀ lam tr i, D.cap lam tr i ≤ 2 * lam) ∧ AreThePiecesOfAppHalfPieces D ∧ 18 ≤ x₀ ∧ c + 7 ≤ 2 ^ x₀ ∧
    (cliqueMachine (c + 2) x₀ Alg).PolyTimeSteps ∧
    CliqueLevels.Solves (cliqueMachine (c + 2) x₀ Alg) (Levels.Gen.K x₀) (Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ ∧
    CliqueLevels.Levels (Levels.Gen.K x₀) (Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ ∧
    CliqueLevels.ComputesLevels (Levels.Gen.K x₀) (CliqueLevels.levelsUnder x₀) ∧
    CliqueLevels.NumberBetween (Levels.Gen.K x₀) (Levels.Gen.e (1 / Real.sqrt 2) x₀) PairsToBound.fractionHalf ∧
    ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (MainTheoremForms.lg (Levels.Gen.K x₀ l))
def TheRecursionMeetsTheHypothesisFrom : Prop :=
  PiecesCounted.HalfPieces → PiecesCounted.MayAssume → RecursionSolves → CliqueLevels.SolvesGrowsWithTheConstant → ThePairsMeetTheClauses → TheRecursionMeetsTheHypothesis
end CountedInstance


