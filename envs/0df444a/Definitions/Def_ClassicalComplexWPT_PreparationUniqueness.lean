-- Prove2me | Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
-- name    : ClassicalComplexWPT_PreparationUniqueness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:10:50.255824+00:00
-- url     : https://prove2.me/theorems/fd4d5d1b-7da5-4740-963a-deb0d7ef0c91
-- title:
--   Preparation Uniqueness
-- statement:
--   Definitions and structural lemmas for Preparation Uniqueness, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ClassicalComplexWPT
noncomputable def constantOneSeq : L1Coeff ℕ := lp.single 1 0 1
noncomputable def preparedTailSeq {n : ℕ} (r : ℝ≥0) (d : ℕ)
    (a : Fin d → Base n → ℂ) (z : Base n) : L1Sequence :=
  ∑ i : Fin d, (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
    lp.single 1 (i : ℕ) (a i z)
end ClassicalComplexWPT


