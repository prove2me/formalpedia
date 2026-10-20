-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
-- name    : OAI_Combinatorics_DiscreteConvexity_FiniteFibers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:32:52.674836+00:00
-- url     : https://prove2.me/theorems/4a5a637a-2242-43f2-95c4-b201ff84c344
-- title:
--   Fibres and keys of a finite set under a key function
-- statement:
--   Let $A$ be a finite set and $\kappa$ a function on $A$ (the key).
--
--   1. **Fibre.** For a key value $b$, the fibre is $A_b=\{a\in A:\kappa(a)=b\}$.
--   2. **Keys.** The set of attained keys is $\kappa(A)$.
--   3. **Membership.** $a\in A_b$ iff $a\in A$ and $\kappa(a)=b$, and $A_b$ is nonempty iff $b\in\kappa(A)$:
--   $$
--   A_b\ne\emptyset\iff b\in\kappa(A).
--   $$
--
--   The fibres over the attained keys partition $A$. Weighted sums over $A$ are split into bins this way.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/FiniteFibers.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FiniteFibers.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite partitions by a key

The fibers indexed by the image of a finite source partition that source.
Filtering the source commutes with taking fibers, so the same partition
identities apply to restrictions of a weighted sum.
-/

namespace TalagrandDiscreteConvexity.FiniteFibers

open scoped BigOperators

variable {α β M : Type*} [DecidableEq β]

/-- The elements of `A` with the specified key. -/
def fiber (A : Finset α) (key : α → β) (b : β) : Finset α :=
  A.filter (fun a => key a = b)

/-- Exactly the keys attained by the finite source. -/
def keys (A : Finset α) (key : α → β) : Finset β :=
  A.image key

@[simp]
theorem mem_fiber {A : Finset α} {key : α → β} {b : β} {a : α} :
    a ∈ fiber A key b ↔ a ∈ A ∧ key a = b :=
  Finset.mem_filter

@[simp]
theorem mem_keys {A : Finset α} {key : α → β} {b : β} :
    b ∈ keys A key ↔ ∃ a ∈ A, key a = b :=
  Finset.mem_image

@[simp]
theorem fiber_nonempty_iff (A : Finset α) (key : α → β) (b : β) :
    (fiber A key b).Nonempty ↔ b ∈ keys A key := by
  simp only [fiber, Finset.filter_nonempty_iff, mem_keys]

variable [AddCommMonoid M]

end TalagrandDiscreteConvexity.FiniteFibers

end OAI


