-- Prove2me | Definitions.Def_SourceProof_4654496346907e7968291676
-- name    : SourceProof_4654496346907e7968291676
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:32.271895+00:00
-- url     : https://prove2.me/theorems/b1d4b5ab-f6f5-57c4-ade5-67026902c01e
-- title:
--   StochLean source theorem: StochLean.quadraticVariationSum_add

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_SourceProof_c900c7734142f37ce8586a84

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0}

end TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_4654496346907e7968291676 (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    quadraticVariationSum π (f + g) = quadraticVariationSum π f +
      quadraticVariationSum π g + 2 * covariationSum π f g := by
  simp only [StochLean.quadraticVariationSum, StochLean.covariationSum, _root_.Prove2MeSourceProof.h_c900c7734142f37ce8586a84,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring
end StochLean


