-- Prove2me | Definitions.Def_ClassicalComplexWPT_NormalSum
-- name    : ClassicalComplexWPT_NormalSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:01:58.654069+00:00
-- url     : https://prove2.me/theorems/9880ab9a-d0fe-47b5-bea3-017ee8b9c37c
-- title:
--   Normal Sum
-- statement:
--   Definitions and structural lemmas for Normal Sum, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalSum.lean

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
variable {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
def seriesTsum (p : I → FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E F :=
  fun n ↦ ∑' i, p i n
def sumTsum (p : I → FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' i, (p i).sum x
end ClassicalComplexWPT


