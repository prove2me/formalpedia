-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
-- name    : OAI_Combinatorics_DiscreteConvexity_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:31:29.813352+00:00
-- url     : https://prove2.me/theorems/5483246b-e299-4f12-bb53-78d14426f31b
-- title:
--   Unions of $k$ members, Boolean cube sets and family indicators
-- statement:
--   Let $X$ be a finite ground set and $0<p<1$. A family is a finite set of subsets of $X$. The $p$-biased measure of a family $\mathcal{D}$ is $\mu_p(\mathcal{D})=\sum_{S\in\mathcal{D}}p^{|S|}(1-p)^{|X\setminus S|}$. A family $\mathcal{G}$ covers $\mathcal{A}$ if every $S\in\mathcal{A}$ contains some $I\in\mathcal{G}$; its cost is $\sum_{I\in\mathcal{G}}p^{|I|}$, and $\mathcal{A}$ is $p$-small if it has a cover of cost at most $\frac12$.
--
--   1. **Union family.** For $k\in\mathbb{N}$, $\mathcal{D}^{\cup k}$ is the family of all unions $D_1\cup\dots\cup D_k$ with every $D_j\in\mathcal{D}$; repetitions are allowed.
--   2. **Cube sets.** A Boolean vector $x\in\{0,1\}^X$ represents the set $\{i:x_i=1\}$.
--   3. **Indicator.** The indicator of $\mathcal{D}$ on the cube is
--   $$
--   \mathbf{1}_{\mathcal{D}}(x)=\begin{cases}1,&\{i:x_i=1\}\in\mathcal{D},\\0,&\text{otherwise}.\end{cases}
--   $$
--
--   The exceptional family consists of the sets contained in no union of $k$ members of $\mathcal{D}$. Talagrand's discrete convexity statement asks that it be small when $\mathcal{D}$ has measure close to $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Model.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite families, containment covers, and exceptional sets

All families are ordinary finite sets: repeated generators carry no extra cost.
In contrast, the members of a union tuple may repeat. The exceptional family
uses containment in a union, without any monotonicity assumption on the input.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- All unions of `k` members of a family. -/
def unionFamily (k : ℕ) (D : Family α) : Family α := by
  classical
  exact Finset.univ.filter (fun S =>
    ∃ f : Fin k → Finset α, (∀ j, f j ∈ D) ∧ unionTuple f = S)

/-- The subset represented by a Boolean coordinate vector. -/
def cubeSet (x : α → Bool) : Finset α :=
  Finset.univ.filter (fun i => x i = true)

/-- The indicator of a family on the Boolean cube. -/
def familyIndicator (D : Family α) (x : α → Bool) : ℝ :=
  if cubeSet x ∈ D then 1 else 0

end
end TalagrandDiscreteConvexity

end OAI


