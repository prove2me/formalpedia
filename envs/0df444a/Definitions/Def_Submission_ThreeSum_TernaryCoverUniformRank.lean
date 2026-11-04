-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
-- name    : Submission_ThreeSum_TernaryCoverUniformRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:43:21.208264+00:00
-- url     : https://prove2.me/theorems/09df5295-2b7b-4fb4-919c-403c189295a7
-- title:
--   Ternary Cover Uniform Rank
-- statement:
--   Definitions and structural lemmas for Ternary Cover Uniform Rank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
def columnSpan {d : ℕ} (v : Fin d → σ → K) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range fun i => fun j => v j i)
variable [Fintype K] [DecidableEq K]
def prescribedEvent {d : ℕ} (v : Fin d → σ → K) (target : Fin d → K) : Finset (σ → K) :=
  univ.filter fun w => ∀ j, HashFamily.hashMap v w j = target j
end ThreeSum.TernaryCoverUniformRank


