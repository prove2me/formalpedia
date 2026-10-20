-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
-- name    : OAI_Combinatorics_DiscreteConvexity_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:31:48.913959+00:00
-- url     : https://prove2.me/theorems/6de7caa8-b07f-4800-a37f-a3216bc938af
-- title:
--   Basic identities for measures, costs, covers, unions and exceptional sets
-- statement:
--   Let $X$ be a finite ground set and $0<p<1$. A family is a finite set of subsets of $X$. The $p$-biased measure of a family $\mathcal{D}$ is $\mu_p(\mathcal{D})=\sum_{S\in\mathcal{D}}p^{|S|}(1-p)^{|X\setminus S|}$. A family $\mathcal{G}$ covers $\mathcal{A}$ if every $S\in\mathcal{A}$ contains some $I\in\mathcal{G}$; its cost is $\sum_{I\in\mathcal{G}}p^{|I|}$, and $\mathcal{A}$ is $p$-small if it has a cover of cost at most $\frac12$. For $k\in\mathbb{N}$, $\mathcal{D}^{\cup k}$ is the family of unions of $k$ members of $\mathcal{D}$, and $\mathcal{E}_k(\mathcal{D})$ is the family of sets contained in no such union.
--
--   1. $\mu_p(\emptyset)=0$, the empty family has cost $0$, and a single generator $I$ has cost $p^{|I|}$.
--   2. Every family covers the empty family.
--   3. Membership: $a\in D_1\cup\dots\cup D_k$ iff $a\in D_j$ for some $j$. $S\in\mathcal{D}^{\cup k}$ iff $S$ is such a union. $S\in\mathcal{E}_k(\mathcal{D})$ iff $S\not\subseteq D_1\cup\dots\cup D_k$ for all $D_j\in\mathcal{D}$.
--   4. Cube sets: $a$ lies in the set of $x$ iff $x_a=1$, and the indicator vector of $S$ represents $S$.
--
--   These are the simplification rules used throughout the argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Basic.lean by skeleton subtraction
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

namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

@[simp] theorem familyMeasure_empty (p : ℝ) :
    familyMeasure p (∅ : Family α) = 0 := by simp [familyMeasure]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_empty (p : ℝ) : cost p (∅ : Family α) = 0 := by
  simp [cost]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_singleton (p : ℝ) (I : Finset α) :
    cost p {I} = p ^ I.card := by simp [cost]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem covers_empty (G : Family α) : Covers G ∅ := by
  intro S hS
  exact False.elim (Finset.notMem_empty S hS)

omit [Fintype α] in
@[simp] theorem mem_unionTuple {k : ℕ} {f : Fin k → Finset α} {a : α} :
    a ∈ unionTuple f ↔ ∃ j, a ∈ f j := by
  simp [unionTuple]

@[simp] theorem mem_unionFamily {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ unionFamily k D ↔
      ∃ f : Fin k → Finset α, (∀ j, f j ∈ D) ∧ unionTuple f = S := by
  classical
  simp [unionFamily]

@[simp] theorem mem_exceptional {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ exceptional k D ↔
      ∀ f : Fin k → Finset α, (∀ j, f j ∈ D) → ¬ S ⊆ unionTuple f := by
  classical
  simp [exceptional]

omit [DecidableEq α] in
@[simp] theorem mem_cubeSet {x : α → Bool} {a : α} :
    a ∈ cubeSet x ↔ x a = true := by simp [cubeSet]

@[simp] theorem cubeSet_decide (S : Finset α) :
    cubeSet (fun a => decide (a ∈ S)) = S := by
  ext a
  simp

end
end TalagrandDiscreteConvexity

end OAI


