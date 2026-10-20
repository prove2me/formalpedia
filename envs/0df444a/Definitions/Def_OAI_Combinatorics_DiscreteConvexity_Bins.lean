-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
-- name    : OAI_Combinatorics_DiscreteConvexity_Bins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:33:19.243726+00:00
-- url     : https://prove2.me/theorems/3357ed3a-2f3e-4e3d-9646-c39fa7c883a5
-- title:
--   Splitting weights into large weights and dyadic bins by size and exponent
-- statement:
--   Let $X$ be finite and $W$ a real weight on subsets of $X$.
--
--   1. **Large weights.** $\mathcal{L}(W)$ consists of the nonempty $U$ with $(1/2)^{64|U|}\le W(U)$.
--   2. **Small weights.** $\mathcal{S}(W)$ consists of the nonempty $U$ with $0<W(U)<(1/2)^{64|U|}$.
--   3. **Bins.** The key of $U\in\mathcal{S}(W)$ is the pair $(|U|,e(W(U)))$ of its size and the dyadic exponent of its weight. The occupied bins are the attained keys, and the bin of a key $b$ is
--   $$
--   \mathcal{S}_b(W)=\{U\in\mathcal{S}(W):\ (|U|,e(W(U)))=b\}.
--   $$
--
--   Large weights pay for their own generators directly. Within a bin all sets have the same size and comparable weights, so the elementary covering lemma applies to each bin.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The generators whose weights pay directly for their cost. -/
noncomputable def largeWeightFamily (W : Finset α → ℝ) : Family α := by
  classical
  exact Finset.univ.filter fun U => U ≠ ∅ ∧ (1 / 2 : ℝ) ^ (64 * U.card) ≤ W U

/-- The remaining nonzero weights; this finite family is partitioned into bins. -/
noncomputable def smallWeightFamily (W : Finset α → ℝ) : Family α := by
  classical
  exact Finset.univ.filter fun U =>
    U ≠ ∅ ∧ 0 < W U ∧ W U < (1 / 2 : ℝ) ^ (64 * U.card)

noncomputable def weightBinKey (W : Finset α → ℝ) (U : Finset α) : ℕ × ℕ :=
  (U.card, binExponent (W U))

noncomputable def occupiedWeightBins (W : Finset α → ℝ) : Finset (ℕ × ℕ) :=
  FiniteFibers.keys (smallWeightFamily W) (weightBinKey W)

noncomputable def weightBin (W : Finset α → ℝ) (b : ℕ × ℕ) : Family α :=
  FiniteFibers.fiber (smallWeightFamily W) (weightBinKey W) b

@[simp] theorem mem_largeWeightFamily {W : Finset α → ℝ} {U : Finset α} :
    U ∈ largeWeightFamily W ↔
      U ≠ ∅ ∧ (1 / 2 : ℝ) ^ (64 * U.card) ≤ W U := by
  classical
  simp [largeWeightFamily]

@[simp] theorem mem_smallWeightFamily {W : Finset α → ℝ} {U : Finset α} :
    U ∈ smallWeightFamily W ↔
      U ≠ ∅ ∧ 0 < W U ∧ W U < (1 / 2 : ℝ) ^ (64 * U.card) := by
  classical
  simp [smallWeightFamily]

end TalagrandDiscreteConvexity

end OAI


