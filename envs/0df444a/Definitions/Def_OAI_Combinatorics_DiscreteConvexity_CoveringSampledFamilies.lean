-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
-- name    : OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:34:39.410892+00:00
-- url     : https://prove2.me/theorems/923ba273-a64c-41c2-8205-11ec126ecc4f
-- title:
--   Sampled pair unions and residual tuple unions
-- statement:
--   Let $H$ be a finite family of subsets of $V$ and let a sample be a set of ordered pairs of edges of $H$.
--
--   1. **Pair union.** A pair $(e,e')$ produces the generator $e\cup e'$.
--   2. **Sampled family.** The set of generators $e\cup e'$ over the sampled pairs (duplicates identified).
--   3. **Residual family.** The unions $e_1\cup\dots\cup e_m$ of injective $m$-tuples of edges none of whose ordered pairs $(e_i,e_j)$ was sampled:
--   $$
--   \Bigl\{\textstyle\bigcup_ie_i:\ (e_i,e_j)\notin\text{sample for all }i,j\Bigr\}.
--   $$
--
--   For every outcome of the sampling, the sampled and residual families together give a cover of the dense sets. Their costs are then controlled in expectation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringSampledFamilies.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringSampledFamilies.lean by skeleton subtraction
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

namespace OAI

/-!
# Deterministic covers from a pair-sampling outcome

Every sampling outcome gives a cover.  The cost bounds count generators
with multiplicity, indexed by ordered pairs or injective ordered tuples.
No independence or probability estimate is needed for these pointwise
statements.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The generator produced by a sampled ordered pair. -/
def pairUnion {H : Family V} (p : PairIndex H) : Finset V := p.1.val ∪ p.2.val

/-- Duplicate unions are identified in the family of sampled generators. -/
noncomputable def sampledFamily (H : Family V) (sample : Sample H) : Family V :=
  sample.image pairUnion

/-- An injective tuple contributes a residual generator exactly when all
of its ordered pair indices were avoided. -/
noncomputable def residualFamily (H : Family V) (m : ℕ) (sample : Sample H) :
    Family V := by
  classical
  exact (Finset.univ.filter
    (fun f : EdgeTuple H m => Disjoint sample (tuplePairs f))).image tupleUnion

@[simp] theorem mem_sampledFamily {H : Family V} {sample : Sample H} {I : Finset V} :
    I ∈ sampledFamily H sample ↔ ∃ p ∈ sample, pairUnion p = I := by
  classical
  simp [sampledFamily]

@[simp] theorem mem_residualFamily {H : Family V} {m : ℕ}
    {sample : Sample H} {I : Finset V} :
    I ∈ residualFamily H m sample ↔
      ∃ f : EdgeTuple H m, Disjoint sample (tuplePairs f) ∧ tupleUnion f = I := by
  classical
  simp [residualFamily]

end TalagrandDiscreteConvexity.Covering

end OAI


