-- Prove2me | Definitions.Def_ChapterLayerNorm
-- name    : ChapterLayerNorm
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:38:40.863816+00:00
-- url     : https://prove2.me/theorems/b24b4653-09df-48ba-8bbc-eb308d7e0832
-- title:
--   Chapter LayerNorm
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLayerNorm.lean`): generated def bundle for ChapterLayerNorm. See BookProof/ChapterLayerNorm.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLayerNorm.lean

import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": layer normalization fixes the gauge

Every transformer block normalizes its activations before the head reads them:
subtract the mean, divide by the standard deviation.  In the language of this
chapter that is a *gauge fixing* followed by a *temperature fixing*, and this
module proves both halves.

* `sum_layerNorm_eq_zero`, `sum_sq_layerNorm` — the normalized vector has zero mean
  and squared length exactly `d`, so it lives on a fixed sphere: the head always
  reads vectors of the same size.
* `layerNorm_add_const`, `layerNorm_smul_pos`, `layerNorm_layerNorm` — the map is
  invariant under the affine reparametrizations `x ↦ ax + c` (`a > 0`) and is
  idempotent: it is a projection onto that sphere.
* `abs_inner_layerNorm_le` — hence Cauchy–Schwarz bounds every score of a
  normalized head by `d`, so the scores have spread at most `2d` and
  `scoreSoftmax_layerNorm_ge` (via `ChapterAttentionRetrieval`) gives every key the
  guaranteed floor `e^{−2βd}/m` of attention.  **Normalization is what keeps the
  temperature of the Born measurement bounded.**

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterLayerNorm

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionRetrieval

variable {d : ℕ}

/-! ## Mean, variance, normalization -/

/-- The mean of the coordinates. -/
def mean (x : Fin d → ℝ) : ℝ := (∑ i, x i) / d

/-- The (biased) variance of the coordinates. -/
def variance (x : Fin d → ℝ) : ℝ := (∑ i, (x i - mean x) ^ 2) / d

/-- **Layer normalization**: centre, then divide by the standard deviation. -/
def layerNorm (x : Fin d → ℝ) (i : Fin d) : ℝ := (x i - mean x) / Real.sqrt (variance x)









/-! ## The normalized vector lives on a sphere -/





/-! ## Invariance and idempotence -/



















/-! ## Bounded scores, bounded temperature -/





end BookProof.ChapterLayerNorm

end


