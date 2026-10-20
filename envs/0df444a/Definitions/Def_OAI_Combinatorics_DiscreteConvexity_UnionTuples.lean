-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_UnionTuples
-- name    : OAI_Combinatorics_DiscreteConvexity_UnionTuples
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:44:14.550696+00:00
-- url     : https://prove2.me/theorems/7ba9d1ca-b0e0-41e5-beaa-db3b27441565
-- title:
--   Flattening and repeating tuples of sets
-- statement:
--   Let $a,b\in\mathbb{N}$.
--
--   1. **Flattening.** An array $(F_{s,t})$ with $s<a$, $t<b$ of subsets of $X$ is read as a tuple of length $ab$ via the standard bijection $\{0,\dots,ab-1\}\cong\{0,\dots,a-1\}\times\{0,\dots,b-1\}$.
--   2. **Repetition.** A tuple $(F_1,\dots,F_b)$ repeated $a$ times gives a tuple of length $ab$ with the same union:
--   $$
--   \bigcup_{s,t}F_t=\bigcup_tF_t .
--   $$
--
--   Grouping $ab$ members into $a$ rows of $b$ members preserves the possible unions. Exceptional sets for $ab$ members can thus be compared with exceptional sets for unions of rows.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/UnionTuples.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/UnionTuples.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling

namespace OAI

/-!
# Grouping and repeating union tuples

Grouping `a * b` entries into `a` rows of length `b` preserves exactly the
possible unions. Repetition is allowed throughout, as in the definition of
the exceptional family. No positivity assumption is needed for grouping.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Flatten a rectangular array using the standard finite product equivalence. -/
def flattenTuple {a b : ℕ} (f : Fin a → Fin b → Finset α) :
    Fin (a * b) → Finset α :=
  fun t => f (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

/-- Repeat the same row tuple `a` times. -/
def repeatTuple (a : ℕ) {b : ℕ} (f : Fin b → Finset α) :
    Fin (a * b) → Finset α :=
  flattenTuple (fun _ : Fin a => f)

end TalagrandDiscreteConvexity

end OAI


