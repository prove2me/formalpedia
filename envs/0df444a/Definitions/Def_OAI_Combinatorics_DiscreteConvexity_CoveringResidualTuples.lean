-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
-- name    : OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:37:38.582659+00:00
-- url     : https://prove2.me/theorems/d52afbf3-a5c9-4368-a1ef-7cf19d60b366
-- title:
--   Total weights of injective and unrestricted edge tuples
-- statement:
--   Let $H$ be a finite family of subsets of $V$, $\rho\in\mathbb{R}$ and $t\in\mathbb{N}$.
--
--   1. **Unrestricted tuples.** For $f:\{1,\dots,t\}\to H$, its union $\bigcup_if(i)$, and the total weight
--   $$
--   A_t=\sum_{f:\{1,\dots,t\}\to H}\rho^{|\bigcup_if(i)|}.
--   $$
--   2. **Injective tuples.** For an injective tuple, the weight $\rho^{|\text{union}|}$, and the sum $T_t$ of these weights over all injective $t$-tuples.
--   3. **Base cases.** For $t=0$ the union is empty and $A_0=T_0=1$.
--
--   The injective sum is bounded by the unrestricted one. The latter satisfies a recurrence obtained by splitting off the first edge.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean by skeleton subtraction
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

namespace OAI

/-!
# The total weight of residual tuples

We bound the sum over injective edge tuples by the sum over all edge tuples.
Splitting an unrestricted tuple into its first edge and its tail gives an
exact weighted recurrence. The per-union extension bound then controls every
step. No nonemptiness assumption on the edge family is needed.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable section

/-- The union of an unrestricted ordered edge tuple. -/
def allTupleUnion {H : Family V} {t : ℕ} (f : Fin t → ↥H) : Finset V :=
  Finset.univ.biUnion (fun i => (f i).val)

/-- Weight of the union of an injective tuple. -/
def tupleWeight {H : Family V} {t : ℕ} (rho : ℝ) (f : EdgeTuple H t) : ℝ :=
  rho ^ (tupleUnion f).card

def tupleWeightSum (H : Family V) (rho : ℝ) (t : ℕ) : ℝ :=
  ∑ f : EdgeTuple H t, tupleWeight rho f

/-- The larger sum in which repeated edges are allowed. -/
def allTupleWeightSum (H : Family V) (rho : ℝ) (t : ℕ) : ℝ :=
  ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card

@[simp] theorem allTupleUnion_zero {H : Family V} (f : Fin 0 → ↥H) :
    allTupleUnion f = ∅ := by
  simp [allTupleUnion]

@[simp] theorem allTupleWeightSum_zero (H : Family V) (rho : ℝ) :
    allTupleWeightSum H rho 0 = 1 := by
  classical
  simp [allTupleWeightSum]

@[simp] theorem tupleWeightSum_zero (H : Family V) (rho : ℝ) :
    tupleWeightSum H rho 0 = 1 := by
  classical
  let : Unique (EdgeTuple H 0) :=
    { default := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      uniq := fun f => Subtype.ext (funext fun i => Fin.elim0 i) }
  simp [tupleWeightSum, tupleWeight, tupleUnion]

end

end TalagrandDiscreteConvexity.Covering

end OAI


