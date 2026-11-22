-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfPrimeNumberTheoremInProgressions
-- name    : Formalism_GL3MeanSquares_PrimePairOfPrimeNumberTheoremInProgressions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:49.218329+00:00
-- url     : https://prove2.me/theorems/c140155c-fe6a-431f-9a4d-23860625982e
-- title:
--   Prime Pair Of Prime Number Theorem In Progressions
-- statement:
--   Definitions and structural lemmas for Prime Pair Of Prime Number Theorem In Progressions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/PrimePairOfPrimeNumberTheoremInProgressions.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_ZeroDensityBox
import Definitions.Def_Formalism_GL3MeanSquares_BoxCountAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.PrimeNumberTheoremConsequences
def liX (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t
def piAP (X : ℝ) (M b : ℕ) : ℕ :=
  ((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card
def IsExcPair {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) : Prop :=
  χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 ∧
    1 - 1 / (8 * Real.log M) < β₁ ∧ β₁ < 1
def mainAP {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (b : ℕ) (X : ℝ) : ℝ :=
  match e with
  | none => liX X / (M.totient : ℝ)
  | some (χ₁, β₁) => (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)
def PNTAPRelW : Prop :=
  ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M →
    ∃ e : Option (DirichletCharacter ℂ M × ℝ),
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2) ∧
      (e = none → ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), ¬ IsExcPair χ₁ β₁) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X
def MeanSquareFromPNT : Prop :=
  PNTAPRelW → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ Formalism.HermitianLattices.WeakMeanSquareEstimates.MeanSquareHypW ε C x₀
def PrimePairOfPrimeNumberTheoremInProgressions : Prop :=
  PNTAPRelW → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Formalism.HermitianLattices.ZeroFreeRegionGL2.ExistsSplitGoodPrimePair ε C x
end Formalism.HermitianLattices.PrimeNumberTheoremConsequences


