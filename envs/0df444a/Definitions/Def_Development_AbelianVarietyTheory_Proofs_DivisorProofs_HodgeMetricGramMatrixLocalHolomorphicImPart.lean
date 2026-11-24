-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:56.670798+00:00
-- url     : https://prove2.me/theorems/8c1320e9-083e-4b23-a63e-31f811a3df4d
-- title:
--   Hodge Metric Gram Matrix Local Holomorphic Im Part
-- statement:
--   Definitions and structural lemmas for Hodge Metric Gram Matrix Local Holomorphic Im Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.HodgeGramLocal
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
end General
def locLog (w₀ w : ℂ) : ℂ := Complex.log (w / w₀) + Complex.log w₀
end GlobalTheory.HodgeGramLocal
namespace GlobalTheory.HodgeGramLocal
variable {n a g : ℕ}
def locEntry (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (j k : Fin g) (x : Fin n → ℂ) : ℂ :=
  τ₀ x j k + ∑ i, locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i)) / (2 * Real.pi * I) *
    ((B i j k : ℤ) : ℂ)
end GlobalTheory.HodgeGramLocal


