-- Prove2me | Definitions.Def_ClassicalComplexWPT_PublicExistence
-- name    : ClassicalComplexWPT_PublicExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:09:45.942461+00:00
-- url     : https://prove2.me/theorems/f79c2e94-f5f1-5c49-8e92-71593e6e6c1a
-- title:
--   Public Existence
-- statement:
--   Definitions and structural lemmas for Public Existence, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace ClassicalComplexWPT
noncomputable def preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) (i : Fin d) : Base n → ℂ :=
  fun z ↦ -((r : ℂ) ^ (d - (i : ℕ))) * normalizedPreparationRemainder p r hr d z i
noncomputable def preparationQuotientEval {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Ambient n → ℂ :=
  fun x ↦ evalL1PowerSeries (normalizedPreparationQuotient p r hr d x.1)
    ((r : ℂ)⁻¹ * x.2)
noncomputable def preparationUnit {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Ambient n → ℂ :=
  fun x ↦ (originWeightedCoeffs p r hr d * (r : ℂ)⁻¹ ^ d) *
    (preparationQuotientEval p r hr d x)⁻¹
end ClassicalComplexWPT


