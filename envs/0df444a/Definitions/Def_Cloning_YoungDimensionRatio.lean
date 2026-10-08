-- Prove2me | Definitions.Def_Cloning_YoungDimensionRatio
-- name    : Cloning_YoungDimensionRatio
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T18:48:45.695708+00:00
-- url     : https://prove2.me/theorems/d02c7020-fff9-4ba8-9a48-f6746024fe61
-- title:
--   Explicit crossing-root dimension product and leading coefficient
-- statement:
--   For nonnegative integers r and k and zero-based indices i<r, j<k, define the positive crossing-root gap $g_{i,j}=r+j-i$. For an arbitrary real row vector, define $D_{r,k}(\mathrm{row})=\prod_{i<r,j<k}(\mathrm{row}_i+g_{i,j})/g_{i,j}$ and $c_{r,k}=\prod_{i<r,j<k}1/(r g_{i,j})$. Empty products equal one. These are explicit analytic definitions, not an asserted identification with representation dimensions.
--
--   This is supporting analytic material for [the paper](https://arxiv.org/abs/2609.35986).
-- source:
--   https://github.com/JWang226/Cloning/blob/cb7b0df616294bd0729dd1ad693421739f01fd0b/formalization/Cloning/YoungDimensionRatio.lean#L29-L53

-- Converted subset of JWang226/Cloning v1.0.0 for Prove2Me.
-- Definitions retained; supporting proofs live in separate solution files.
-- Original release source and statement hypotheses are preserved.
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete asymptotics of the crossing-root Weyl dimension product

For an `r`-row label in ambient dimension `r+k`, the manuscript's explicit
dimension-ratio expression is the product of `(rowᵢ+j-i)/(j-i)` over crossing
roots. This file defines that actual finite product and derives its uniform
relative-error bound directly from the row lengths. No dimension-ratio
convergence or product approximation is assumed.

The identification of this explicit Weyl product with dimensions of the
particular representation spaces is a separate representation-theoretic
statement. This file proves the analytic input once that formula is used.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungDimensionRatio

/-- The positive-root gap `j-i`, using zero-based indices on either side
of the rank boundary. Ambient dimension is `r+k`. -/
def crossingGap {r k : ℕ} (a : Fin r × Fin k) : ℝ :=
  (r : ℝ) + (a.2.val : ℝ) - (a.1.val : ℝ)





/-- The manuscript's concrete crossing-root dimension-ratio product. -/
def dimensionRatio (r k : ℕ) (row : Fin r → ℝ) : ℝ :=
  ∏ a : Fin r × Fin k, (row a.1 + crossingGap a) / crossingGap a

/-- The exact leading coefficient `c_{r,r+k}`. -/
def leadingConstant (r k : ℕ) : ℝ :=
  ∏ a : Fin r × Fin k, 1 / ((r : ℝ) * crossingGap a)





















end Cloning.YoungDimensionRatio


