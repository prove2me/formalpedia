-- Prove2me | Definitions.Def_ClassicalComplexWPT_PreparationSequences
-- name    : ClassicalComplexWPT_PreparationSequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:08:42.660743+00:00
-- url     : https://prove2.me/theorems/32d27b6b-fbe8-5474-93dd-c0d597a6ec0a
-- title:
--   Preparation Sequences
-- statement:
--   Definitions and structural lemmas for Preparation Sequences, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
namespace ClassicalComplexWPT
noncomputable def normalizedPreparationTail {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ analyticNormalizedCoefficientMap p r hr d z - monomialSeq d
noncomputable def normalizedPreparationQuotient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ seqDivisionQuotientGlobal d
    (normalizedPreparationTail p r hr d z, monomialSeq d)
noncomputable def normalizedPreparationRemainder {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ seqDivisionRemainderGlobal d
    (normalizedPreparationTail p r hr d z, monomialSeq d)
end ClassicalComplexWPT


