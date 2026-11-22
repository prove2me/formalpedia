-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
-- name    : Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:42.986659+00:00
-- url     : https://prove2.me/theorems/f11b13e0-41ed-4534-bc48-d7d56d0c4ca6
-- title:
--   Prime Pair Of Box And Weak Mean Square Hypotheses
-- statement:
--   Definitions and structural lemmas for Prime Pair Of Box And Weak Mean Square Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/PrimePairOfBoxAndWeakMeanSquareHypotheses.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.WeakMeanSquareEstimates
def MeanSquareHypW (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)
def MeanSquareWeaken : Prop :=
  ∀ ε C x₀ : ℝ, MeanSquareHyp ε C x₀ → MeanSquareHypW ε C x₀
def PrimePairOfBoxAndWeakMeanSquareHypotheses : Prop :=
  ∀ ε C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < C₂ → 0 < C₄ →
    BoxCountHyp C₂ → BoxTailHyp ε C₂' x₂ → MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ExistsSplitGoodPrimePair ε C₂' x
end Formalism.HermitianLattices.WeakMeanSquareEstimates


