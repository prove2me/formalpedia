-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
-- name    : OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:38:34.861958+00:00
-- url     : https://prove2.me/theorems/1e24a6ef-fc50-4aa7-8c83-bda5ed720b74
-- title:
--   Numerical parameters of the elementary covering lemma
-- statement:
--   For $h,r\in\mathbb{N}$ define
--   $$
--   m(h)=2^{12h},\qquad T(h)=2^{4h},\qquad p(h)=2^{-8h},\qquad A(r,h)=4h+13rh .
--   $$
--
--   $m(h)$ is the number of edges in a residual tuple, $T(h)$ the threshold for large weighted degree, $p(h)$ the sampling probability of each ordered pair, and $A(r,h)$ an exponent bounding one regular extension factor. The sampling probability satisfies $0<p(h)\le1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandDiscreteConvexity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples

namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

/-- Number of distinct edges in a residual tuple. -/
def m (h : ℕ) : ℕ := 2 ^ (12 * h)

/-- Threshold for a large weighted degree. -/
def T (h : ℕ) : ℝ := 2 ^ (4 * h)

/-- Independent sampling probability for each ordered pair. -/
noncomputable def p (h : ℕ) : ℝ := (2 ^ (8 * h))⁻¹

/-- Exponent bounding one regular extension factor. -/
def A (r h : ℕ) : ℕ := 4 * h + 13 * r * h

theorem p_pos (h : ℕ) : 0 < p h := by
  unfold p
  positivity

theorem p_nonneg (h : ℕ) : 0 ≤ p h := (p_pos h).le

theorem p_le_one (h : ℕ) : p h ≤ 1 := by
  unfold p
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI


